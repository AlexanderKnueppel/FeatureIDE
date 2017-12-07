/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 *
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.featurehouse.contracts;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.nio.file.FileVisitResult;
import java.nio.file.FileVisitor;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.prop4j.And;
import org.prop4j.ContractNodeReader;
import org.prop4j.ExpressionLiteral;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.NodeWriter;
import org.prop4j.Or;
import org.prop4j.solver.ModifiableSolver;
import org.prop4j.solver.SatInstance;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.featurehouse.FeatureHouseCorePlugin;
import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.editing.NodeCreator;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.functional.Functional.IFunction;

/**
 * This class is responsible for processing contracts (of metaproducts with dispatcher methods).
 *
 * @author Stefan Krueger
 * @author Sebastian Krieter
 */
public class ContractProcessor {

	private static final FeatureHouseCorePlugin LOGGER = FeatureHouseCorePlugin.getDefault();
	private static final String FMPLACEHOLDER = "%FM.%";
	private final static Set<String> postCompiledFiles = new HashSet<String>();

	public static void clearFiles() {
		postCompiledFiles.clear();
	}

	/**
	 * @param featureModel
	 * @param outputPath
	 * @throws IOException
	 */
	public static void performContractOptimizations(final IFeatureModel featureModel, final String outputPath) throws IOException {
		final Set<Object> featureNamesLower = new HashSet<>(Functional.toList(Functional.map(featureModel.getFeatures(), new IFunction<IFeature, Object>() {
			@Override
			public String invoke(IFeature t) {
				return t.getName().toLowerCase();
			}
		})));

		final Set<Object> deadFeaturesLower = new HashSet<>();
		for (final IFeature deadFeature : featureModel.getAnalyser().getDeadFeatures()) {
			deadFeaturesLower.add(deadFeature.getName().toLowerCase());
		}
		final Set<Object> coreFeaturesLower = new HashSet<>();
		for (final IFeature coreFeature : featureModel.getAnalyser().getCoreFeatures()) {
			coreFeaturesLower.add(coreFeature.getName().toLowerCase());
		}
		coreFeaturesLower.add(NodeCreator.varTrue);
		deadFeaturesLower.add(NodeCreator.varFalse);

		featureNamesLower.add(NodeCreator.varTrue);
		featureNamesLower.add(NodeCreator.varFalse);

		final Path path = Paths.get(outputPath);
		final FileVisitor<Path> fileVisit = new FileVisitor<Path>() {

			@Override
			public FileVisitResult preVisitDirectory(Path dir, BasicFileAttributes attrs) throws IOException {
				return FileVisitResult.CONTINUE;
			}

			@Override
			public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) throws IOException {
				if (attrs.isRegularFile()) {
					final String fileName = file.getFileName().toString();
					final int indexOfDot = fileName.lastIndexOf('.');
					if ((indexOfDot > 0) && "java".equals(fileName.substring(indexOfDot + 1))) {
						final String content = new String(Files.readAllBytes(file), "UTF-8");
						final StringBuilder newContent = new StringBuilder(content.length());
						/*
						 * Contracts can either be abstract or concrete. If the contract is abstract, clauses look like this: (requires|ensures)_abs $nameR; def
						 * $nameR = C1 && ... Cn; In order to get C1 ... Cn, we look for the requires_abs and ensures_abs keywords and then get the actual
						 * clauses by cutting off everything before the next equal sign. If the contract is concrete, it looks like this: requires|ensures C1;
						 * ... requires|ensures Cn; Here, we look for the requires and ensures keywords and make a cut after the next whitespace.
						 */
						final String abstractContractsClauseRegex = "\\s+(requires_abs|ensures_abs)\\s+[^;]*;\\s+def[^;]*;";
						final String concreteContractsClauseRegex = "(requires|ensures)\\s+[^;]*;";
						Pattern clausePattern = Pattern.compile(abstractContractsClauseRegex);
						Matcher clauseMatcher = clausePattern.matcher(content);
						final boolean fileHasAbstractContracts = clauseMatcher.find();
						if (!fileHasAbstractContracts) {
							clausePattern = Pattern.compile(concreteContractsClauseRegex);
							clauseMatcher = clausePattern.matcher(content);
							if (!clauseMatcher.find()) {
								return FileVisitResult.CONTINUE;
							}
						}
						clauseMatcher.reset();
						int pos = 0;
						while (clauseMatcher.find()) {
							final int start = clauseMatcher.start();
							final int end = clauseMatcher.end();
							final String abstractClause = content.substring(start, end);
							final int clauseLength = abstractClause.length();
							final int indexOfClause = abstractClause.indexOf(fileHasAbstractContracts ? '=' : ' ');
							final String clauseContent = abstractClause.substring(indexOfClause + 1, clauseLength - 1).trim();

							final ContractNodeReader conNodeReader = new ContractNodeReader();
							final Node oldClauseNode = conNodeReader.parseStringToNode(clauseContent);
							Node clauseNode = oldClauseNode.toRegularCNF();
							final List<Node> collectNodes;
							final Node[] andChildren = clauseNode.getChildren();
							collectNodes = new ArrayList<Node>(andChildren.length);
							for (int j = 0; j < andChildren.length; j++) {
								final Node childOfAnd = andChildren[j];
								handleLiteralsAndOrClauses(deadFeaturesLower, coreFeaturesLower, featureNamesLower, clauseNode, collectNodes, childOfAnd);
							}

							if (collectNodes.isEmpty()) {
								clauseNode = new Literal(NodeCreator.varTrue);
							} else {
								clauseNode = new And(collectNodes.toArray(new Node[0]));
								try {
									final SatInstance si = new SatInstance(null, SatInstance.getDistinctVariableObjects(clauseNode));
									final ModifiableSolver redundantSat = new ModifiableSolver(si);
									final List<Node> newNodeChildren = new ArrayList<>();
									final List<IConstr> constraintMarkers = redundantSat.addCNF(clauseNode.getChildren());

									int i = -1;
									for (final IConstr constraint : constraintMarkers) {
										i++;
										if (constraint != null) {
											redundantSat.removeConstraint(constraint);
											final Node constraintNode = clauseNode.getChildren()[i];
											if (!redundantSat.isImplied(constraintNode.getChildren())) {
												redundantSat.addCNF(new Node[] { constraintNode });
												newNodeChildren.add(constraintNode);
											}
										}
									}
									clauseNode = new And(newNodeChildren.toArray(new Node[0]));
								} catch (final ContradictionException e) {
									Logger.logError(e);
								}
							}
							final NodeWriter nw = new NodeWriter(clauseNode);
							nw.setSymbols(NodeWriter.jmlSymbols);
							final String optimizedNode = nw.nodeToString();

							System.err.println(" Before: " + clauseContent);
							System.err.println("After : " + optimizedNode);
							// 31 nextDay_Interest, true entfernen; 32 siehe 31
							final int offset = start + indexOfClause + 1;

							newContent.append(content.substring(pos, offset));
							newContent.append(" ");
							newContent.append(optimizedNode);
							newContent.append(";");
							pos = start + clauseLength;
						}
						if (pos > 0) {
							newContent.append(content.substring(pos, content.length()));
							Files.write(file, newContent.toString().getBytes("UTF-8"), StandardOpenOption.TRUNCATE_EXISTING, StandardOpenOption.WRITE);
						}
					}
				}
				return FileVisitResult.CONTINUE;

			}

//			private List<String> iterateOverClauseNode(Node clauseNode) {
//				List<String> nodeNames = new ArrayList<String>();
//				nodeNames.add(clauseNode.toString());
//				LinkedList<Node> nodes = new LinkedList<>();
//				nodes.add(clauseNode);
//				while (!nodes.isEmpty()) {
//					Node curNode = nodes.removeFirst();
//					final Node[] nodeChildren = curNode.getChildren();
//					if (nodeChildren != null) {
//						nodes.addAll(Arrays.asList(nodeChildren));
//					}
//					if (curNode instanceof ExpressionLiteral) {
//						nodeNames.add(((ExpressionLiteral) curNode).getExpression());
//					} else {
//						nodeNames.add(curNode.toString());
//					}
//				}
//				Collections.reverse(nodeNames);
//				return nodeNames;
//			}

			private void handleLiteralsAndOrClauses(final Set<Object> deadFeatures, final Set<Object> coreFeaturesLower, Set<Object> featureNamesLower,
					Node clauseNode, final List<Node> newAndNodes, Node childOfAnd) {
				boolean expTrue = false;
				final List<Node> nodes;
				final Node[] orChildren = childOfAnd.getChildren();
				nodes = new ArrayList<Node>(orChildren.length);
				for (int k = 0; k < orChildren.length; k++) {
					final Literal childOfOr = (Literal) orChildren[k];
					if (handleLiteral(deadFeatures, coreFeaturesLower, featureNamesLower, nodes, childOfOr)) {
						expTrue = true;
					}
				}
				if (nodes.size() > 0) {
					newAndNodes.add(new Or(nodes.toArray(new Node[0])));
				} else if (!expTrue) {
					newAndNodes.clear();
					newAndNodes.addAll(Arrays.asList(clauseNode.getChildren()));
					LOGGER.logInfo("Contract optimization failed. Clause is unsatisfiable.");
				}
			}

			private boolean handleLiteral(final Set<Object> deadFeatures, final Set<Object> coreFeaturesLower, Set<Object> featureNamesLower,
					final List<Node> nodes, Literal childOfOr) {
				if (childOfOr instanceof ExpressionLiteral) {
					if (childOfOr.positive) {
						nodes.add(new Literal(((ExpressionLiteral) childOfOr).getExpression(), childOfOr.positive));
					} else {
						nodes.add(new Literal("(" + ((ExpressionLiteral) childOfOr).getExpression() + ")", childOfOr.positive));
					}
				} else {
					if (featureNamesLower.contains(childOfOr.var)) {
						if (childOfOr.positive) {
							if (coreFeaturesLower.contains(childOfOr.var)) {
								nodes.clear();
								return true;
							}
							if (!deadFeatures.contains(childOfOr.var)) {
								nodes.add(new Literal("FM.FeatureModel." + childOfOr.var, true));
							}
						} else {
							if (deadFeatures.contains(childOfOr.var)) {
								nodes.clear();
								return true;
							}
							if (!coreFeaturesLower.contains(childOfOr.var)) {
								nodes.add(new Literal("FM.FeatureModel." + childOfOr.var, false));
							}
						}
					}
				}
				return false;
			}

			@Override
			public FileVisitResult visitFileFailed(Path file, IOException exc) throws IOException {
				LOGGER.logError("Cannot read file " + file.toString(), exc);
				return FileVisitResult.TERMINATE;
			}

			@Override
			public FileVisitResult postVisitDirectory(Path dir, IOException exc) throws IOException {
				return FileVisitResult.CONTINUE;
			}
		};
		Files.walkFileTree(path, fileVisit);
	}

	public static void postComposeForMetaProductsWithDispatcherMethods(IFile file) throws CoreException, IOException {
		final String fileLocation = file.getLocation().toOSString();
		if (postCompiledFiles.add(fileLocation)) {
			final String fileContent = new String(Files.readAllBytes(Paths.get(fileLocation)), file.getCharset());
			final Pattern p = Pattern.compile(
					"([/][*][@].*(ensures_abs|requires_abs|invariant|assignable_abs)\\s+.*[*][/])|([/][/][@].*(ensures_abs|requires_abs|invariant|assignable_abs)\\s+.*$)",
					Pattern.DOTALL);
			if (p.matcher(fileContent).find()) {
				final StringBuilder contentEditor = new StringBuilder(fileContent);

				final Node node = NodeCreator.createNodes(CorePlugin.getFeatureProject(file).getFeatureModel(), false).toRegularCNF();

				final Node[] andChildren = node.getChildren();
				int removalCount = 0;
				for (int i = 0; i < andChildren.length; i++) {
					final Node andChild = andChildren[i];

					int absoluteValueCount = 0;
					boolean valid = true;

					final Literal[] children = Arrays.copyOf(andChild.getChildren(), andChild.getChildren().length, Literal[].class);
					for (int j = 0; j < children.length; j++) {
						final Literal literal = children[j];

						if ("True".equals(literal.var.toString())) {
							if (literal.positive) {
								valid = false;
							} else {
								absoluteValueCount++;
								children[j] = null;
							}
						} else if ("False".equals(literal.var.toString())) {
							if (literal.positive) {
								absoluteValueCount++;
								children[j] = null;
							} else {
								valid = false;
							}
						} else {
							// remember when you/we merge fork and master that this was not part of Sebastian's extension
							literal.var = ((String) literal.var).toLowerCase();
						}
					}

					if (valid) {
						if (absoluteValueCount > 0) {
							final Literal[] newChildren = new Literal[children.length - absoluteValueCount];
							int k = 0;
							for (int j = 0; j < children.length; j++) {
								final Literal literal = children[j];
								if (literal != null) {
									newChildren[k++] = literal;
								}
							}
							andChild.setChildren(newChildren);
						}
					} else {
						andChildren[i] = null;
						removalCount++;
					}

				}

				if (removalCount > 0) {
					final Node[] newChildren = new Node[andChildren.length - removalCount];
					int k = 0;
					for (int j = 0; j < andChildren.length; j++) {
						final Node finalNode = andChildren[j];
						if (finalNode != null) {
							newChildren[k++] = finalNode;
						}
					}
					node.setChildren(newChildren);
				}

				final NodeWriter nw = new NodeWriter(node);
				nw.setSymbols(NodeWriter.jmlSymbols);
				nw.setPrefix("FM.FeatureModel.");
				final String nodeToString = nw.nodeToString();

				final String featuremodel = "\n\t/*@ public invariant " + nodeToString + "; @*/\n";
				final ASTParser astp = ASTParser.newParser(AST.JLS8);

				astp.setSource(fileContent.toCharArray());
				astp.setKind(ASTParser.K_COMPILATION_UNIT);

				final CompilationUnit cu = (CompilationUnit) astp.createAST(null);
				final PostCompiledFileVisitor postCompiledVisitor = new PostCompiledFileVisitor(contentEditor, featuremodel);
				cu.accept(postCompiledVisitor);
				final String newContent =
					postCompiledVisitor.hasConstructor ? contentEditor.toString().replace(FMPLACEHOLDER, nodeToString) : contentEditor.toString();
				file.setContents(new ByteArrayInputStream(newContent.getBytes(file.getCharset())), false, true, null);
			}
		}
	}

	private static final class PostCompiledFileVisitor extends ASTVisitor {

		private boolean hasConstructor = false;
		private final StringBuilder contentEditor;
		private final String featuremodel;

		public PostCompiledFileVisitor(StringBuilder contentEditor, String featuremodel) {
			super();
			this.contentEditor = contentEditor;
			this.featuremodel = featuremodel;
		}

		@Override
		public boolean visit(MethodDeclaration node) {
			if (!hasConstructor && node.isConstructor()) {
				hasConstructor = true;
			}
			return super.visit(node);
		}

		@Override
		public boolean visit(TypeDeclaration node) {
			contentEditor.insert((node.getStartPosition() + node.getLength()) - 1, featuremodel);
			return super.visit(node);
		}

	}

}
