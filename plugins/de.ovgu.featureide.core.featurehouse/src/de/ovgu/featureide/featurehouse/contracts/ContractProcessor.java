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
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedList;
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

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.featurehouse.FeatureHouseCorePlugin;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.editing.NodeCreator;

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
	public static void performContractOptimizations(final FeatureModel featureModel, final String outputPath) throws IOException {
		final Set<String> deadFeaturesLower = new HashSet<String>();
		for (Feature deadFeature : featureModel.getAnalyser().getDeadFeatures()) {
			deadFeaturesLower.add(deadFeature.getName().toLowerCase());
		}
		final Set<Object> coreFeatures = new HashSet<Object>();
		for (Feature coreFeature : featureModel.getAnalyser().getCoreFeatures()) {
			coreFeatures.add(coreFeature.getName().toLowerCase());
		}
		coreFeatures.add(NodeCreator.varTrue);
		
		Path path = Paths.get(outputPath);
		FileVisitor<Path> fileVisit = new FileVisitor<Path>(){
		
			@Override
			public FileVisitResult preVisitDirectory(Path dir, BasicFileAttributes attrs) throws IOException {
				return FileVisitResult.CONTINUE;
			}

			@Override
			public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) throws IOException {
				if (attrs.isRegularFile()) {
					final String fileName = file.getFileName().toString();
					final int indexOfDot = fileName.lastIndexOf('.');
					if (indexOfDot > 0 && "java".equals(fileName.substring(indexOfDot+ 1))) {
						final String content = new String(Files.readAllBytes(file), "UTF-8");
						final StringBuilder newContent = new StringBuilder(content.length());
						/*
						 * Contracts can either be abstract or concrete.
						 * 
						 * If the contract is abstract, clauses look like this:
						 * (requires|ensures)_abs $nameR;
						 * def $nameR = C1 && ... Cn;
						 * In order to get C1 ... Cn, we look for the requires_abs and ensures_abs keywords 
						 * and then get the actual clauses by cutting off everything before the next equal sign.
						 *								  
						 * If the contract is concrete, it looks like this:
						 *  requires|ensures C1;
						 *  	...
						 *  requires|ensures Cn;
						 *  Here, we look for the requires and ensures keywords and make a cut after the next whitespace.
						 *  
						 */
						String abstractContractsClauseRegex = "\\s+(requires_abs|ensures_abs)\\s+[^;]*;\\s+def[^;]*;";
						String concreteContractsClauseRegex = "(requires|ensures)\\s+[^;]*;";
						Pattern clausePattern = Pattern.compile(abstractContractsClauseRegex);
						Matcher clauseMatcher = clausePattern.matcher(content);
						boolean fileHasAbstractContracts = clauseMatcher.find();
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
							int start = clauseMatcher.start();
							int end = clauseMatcher.end();
							String abstractClause = content.substring(start, end);
							final int clauseLength = abstractClause.length();
							int indexOfClause = abstractClause.indexOf(fileHasAbstractContracts ? '=' : ' ');
							String clauseContent = abstractClause.substring(indexOfClause + 1, clauseLength - 1).trim();
							
							ContractNodeReader conNodeReader = new ContractNodeReader();
							Node oldClauseNode = conNodeReader.parseStringToNode(clauseContent);
							Node clauseNode = oldClauseNode.toCNF();
//							List<String> nodeNames = iterateOverClauseNode(clauseNode);
							final List<Node> collectNodes;
							if (clauseNode instanceof And) {
								final Node[] andChildren = clauseNode.getChildren();
								collectNodes = new ArrayList<Node>(andChildren.length);
								for (int j = 0; j < andChildren.length; j++) {
									Node childOfAnd = andChildren[j];
									handleLiteralsAndOrClauses(deadFeaturesLower, coreFeatures, clauseNode, collectNodes, childOfAnd);
								}
							} else {
								collectNodes = new ArrayList<Node>(1);
								handleLiteralsAndOrClauses(deadFeaturesLower, coreFeatures, clauseNode, collectNodes, clauseNode);
							}
							
							if (collectNodes.isEmpty()) {
								clauseNode = new Literal("true");
							} else {
								clauseNode = new And(collectNodes.toArray(new Node[0]));
							}
							String optimizedNode = NodeWriter.nodeToString(clauseNode, NodeWriter.jmlSymbols);
							
							System.out.println();  
							System.out.println(" Before: " + clauseContent);
							System.out.println("After : " + optimizedNode);
							 // 31 nextDay_Interest, true entfernen; 32 siehe 31
							int offset = start + indexOfClause + 1;
							
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

			private List<String> iterateOverClauseNode(Node clauseNode) {
				List<String> nodeNames = new ArrayList<String>();
				nodeNames.add(clauseNode.toString());
				LinkedList<Node> nodes = new LinkedList<>();
				nodes.add(clauseNode);
				while (!nodes.isEmpty()) {
					Node curNode = nodes.removeFirst();
					final Node[] nodeChildren = curNode.getChildren();
					if (nodeChildren != null) {
						nodes.addAll(Arrays.asList(nodeChildren));
					}
					if (curNode instanceof ExpressionLiteral) {
						nodeNames.add(((ExpressionLiteral) curNode).getExpression());
					} else {
						nodeNames.add(curNode.toString());
					}
				}
				Collections.reverse(nodeNames);
				return nodeNames;
			}
			
			private void handleLiteralsAndOrClauses(final Set<String> deadFeatures, final Set<Object> coreFeatures, Node clauseNode, final List<Node> newAndNodes, Node childOfAnd) {
				boolean expTrue = false;
				final List<Node> nodes;
				if (childOfAnd instanceof Or) {
					final Node[] orChildren = childOfAnd.getChildren();
					nodes = new ArrayList<Node>(orChildren.length);
					for (int k = 0; k < orChildren.length; k++) {
						Literal childOfOr = (Literal) orChildren[k];
						if (handleLiteral(deadFeatures, coreFeatures, nodes, childOfOr)) {
							expTrue = true;
						}
					}
				} else {
					nodes = new ArrayList<Node>(1);
					if (handleLiteral(deadFeatures, coreFeatures, nodes, (Literal)childOfAnd)) {
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

			private boolean handleLiteral(final Set<String> deadFeatures, final Set<Object> coreFeatures, final List<Node> nodes, Literal childOfOr) {
				if (childOfOr instanceof ExpressionLiteral) {
					if (childOfOr.positive) {
						nodes.add(new Literal(((ExpressionLiteral)childOfOr).getExpression(), childOfOr.positive));
					} else {
//						if (!expression.contains(" ")) {
//							nodes.add(new Literal(expression, childOfOr.positive));
//						} else {
							nodes.add(new Literal("(" + ((ExpressionLiteral)childOfOr).getExpression() + ")", childOfOr.positive));
//						}
					}
				} else {
					if (childOfOr.positive && featureModel.getFeatureNames().contains(childOfOr)) {
						if (coreFeatures.contains(childOfOr.var)) {
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
						if (!coreFeatures.contains(childOfOr.var)) {
							nodes.add(new Literal("FM.FeatureModel." + childOfOr.var, false));
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
			Pattern p = Pattern.compile("([/][*][@].*(ensures_abs|requires_abs|invariant|assignable_abs)\\s+.*[*][/])|([/][/][@].*(ensures_abs|requires_abs|invariant|assignable_abs)\\s+.*$)", Pattern.DOTALL); 
			if (p.matcher(fileContent).find()) {
				final StringBuilder contentEditor = new StringBuilder(fileContent);
				
				Node node = NodeCreator.createNodes(CorePlugin.getFeatureProject(file).getFeatureModel(), false).toCNF();
				if (node instanceof Or) {
					node = new And(node);
				} else if (node instanceof Literal) {
					node = new And(new Or(node));
				}
				
				Node[] andChildren = node.getChildren();
				int removalCount = 0;
				for (int i = 0; i < andChildren.length; i++) {
					Node andChild = andChildren[i];
					
					if (andChild instanceof Or) {
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
								//remember when you/we merge fork and master that this was not part of Sebastian's extension
								literal.var = ((String)literal.var).toLowerCase();
							}
						}

						if (valid) {
							if (absoluteValueCount > 0) {
								Literal[] newChildren = new Literal[children.length - absoluteValueCount];
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
					} else {
						final Literal literal = (Literal) andChild;
						if ("True".equals(literal.var.toString()) || "False".equals(literal.var.toString())) {
							andChildren[i] = null;
							removalCount++;
						} else {
							//remember when you/we merge fork and master that this was not part of Sebastian's extension
							literal.var = ((String)literal.var).toLowerCase();
						}
					}
				}	
				
				if (removalCount > 0) {
					Node[] newChildren = new Node[andChildren.length - removalCount];
					int k = 0;
					for (int j = 0; j < andChildren.length; j++) {
						final Node finalNode = andChildren[j];
						if (finalNode != null) {
							newChildren[k++] = finalNode;
						}
					}
					node.setChildren(newChildren);
				}
				
				final String nodeToString = NodeWriter.nodeToString(node, NodeWriter.javaSymbols, "FM.FeatureModel.");
				final String featuremodel = "\n\t/*@ public invariant " + nodeToString + "; @*/\n";
				final ASTParser astp = ASTParser.newParser(AST.JLS4);
				
				astp.setSource(fileContent.toCharArray());
				astp.setKind(ASTParser.K_COMPILATION_UNIT);
		 
				final CompilationUnit cu = (CompilationUnit) astp.createAST(null);				
				final PostCompiledFileVisitor postCompiledVisitor = new PostCompiledFileVisitor(contentEditor, featuremodel);
				cu.accept(postCompiledVisitor);
				String newContent = postCompiledVisitor.hasConstructor ? contentEditor.toString().replace(FMPLACEHOLDER, nodeToString) : contentEditor.toString(); 
				file.setContents(new ByteArrayInputStream(newContent.getBytes(file.getCharset())), false, true, null);
			}
		}
	}
	
	private static final class PostCompiledFileVisitor extends ASTVisitor {
			
			private boolean hasConstructor = false;
			private StringBuilder contentEditor;
			private String featuremodel;
	
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
				contentEditor.insert(node.getStartPosition() + node.getLength() - 1, featuremodel);
				return super.visit(node);
			}
	
	}

	
	
}
