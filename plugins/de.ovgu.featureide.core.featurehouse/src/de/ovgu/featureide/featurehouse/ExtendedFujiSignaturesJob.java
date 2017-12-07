/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.featurehouse;

import static de.ovgu.featureide.fm.core.localization.StringTable.FUJI_SIGNATURES_LOADED_;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map.Entry;

import org.eclipse.core.resources.IResource;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.core.JavaProject;

import AST.ASTNode;
import AST.Access;
import AST.BodyDecl;
import AST.ClassDecl;
import AST.ClassInstanceExpr;
import AST.CompilationUnit;
import AST.ConstructorAccess;
import AST.ConstructorDecl;
import AST.FieldDeclaration;
import AST.ImportDecl;
import AST.InterfaceDecl;
import AST.List;
import AST.MemberClassDecl;
import AST.MemberInterfaceDecl;
import AST.MethodAccess;
import AST.MethodDecl;
import AST.ParameterDeclaration;
import AST.Program;
import AST.TypeAccess;
import AST.TypeDecl;
import AST.VarAccess;
import beaver.Symbol;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTClassFragment;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.fstmodel.IRoleElement;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractMethodSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.base.FOPFeatureData;
import de.ovgu.featureide.core.signature.base.FeatureDataConstructor;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiClassSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiFieldSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiMethodSignature;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import fuji.Composition;
import fuji.Main;
import fuji.SPLStructure;

/**
 * Loads the signatures from Fuji.
 *
 * @author Sebastian Krieter
 * @author Marcus Pinnecke
 */
@Deprecated
@SuppressWarnings("restriction")
public class ExtendedFujiSignaturesJob implements LongRunningMethod<ProjectSignatures> {

	private static final class SignatureReference {
		private final HashMap<Integer, FOPFeatureData> ids = new HashMap<>();
		private final AbstractSignature sig;

		public SignatureReference(AbstractSignature sig) {
			this.sig = sig;
		}

		public final FOPFeatureData[] getFeatureData() {
			final FOPFeatureData[] ret = new FOPFeatureData[ids.size()];
			int i = -1;
			for (final FOPFeatureData id : ids.values()) {
				ret[++i] = id;
			}
			return ret;
		}

		public final void addID(FOPFeatureData featureData) {
			if (!ids.containsKey(featureData.getID())) {
				ids.put(featureData.getID(), featureData);
			}
		}

		public final AbstractSignature getSig() {
			return sig;
		}
	}

	public static final class SignatureMethodAccess {

		private final int featureID;
		private final AbstractSignature absSig;

		public int getFeatureID() {
			return featureID;
		}

		public AbstractSignature getAbsSig() {
			return absSig;
		}

		@Override
		public boolean equals(Object arg0) {
			if (arg0 == this) {
				return true;
			}
			if (!(arg0 instanceof SignatureMethodAccess)) {
				return false;
			}
			final SignatureMethodAccess comp = (SignatureMethodAccess) arg0;
			if ((featureID != comp.featureID) || !absSig.equals(comp.absSig)) {
				return false;
			}
			return true;
		}

		@Override
		public int hashCode() {
			int hashCode = featureID;
			hashCode = (37 * hashCode) + absSig.hashCode();
			return hashCode;
		}

		@Override
		public String toString() {
			return featureID + "; " + absSig.toString();
		}

		public SignatureMethodAccess(int featureID, AbstractSignature absSig) {
			this.featureID = featureID;
			this.absSig = absSig;
		}
	}

	private static class ExtendedSignature {

		private final AbstractSignature sig;
		private final int featureID;

		public ExtendedSignature(AbstractSignature sig, int featureID) {
			this.sig = sig;
			this.featureID = featureID;
		}

		@Override
		public int hashCode() {
			return (37 * featureID) + sig.hashCode();
		}

		@Override
		public boolean equals(Object arg0) {
			if (arg0 == this) {
				return true;
			}
			if (!(arg0 instanceof ExtendedSignature)) {
				return false;
			}
			final ExtendedSignature comp = (ExtendedSignature) arg0;
			if ((comp.featureID == featureID) && comp.sig.equals(sig)) {
				return false;
			}
			return true;
		}

		@Override
		public String toString() {
			return featureID + " - " + sig.getFullName();
		}

	}

	private final IFeatureProject featureProject;
	private final ProjectSignatures projectSignatures;
	private final FeatureDataConstructor featureDataConstructor;

	private final HashMap<AbstractSignature, SignatureReference> signatureSet = new HashMap<AbstractSignature, SignatureReference>();
	private final HashMap<String, AbstractSignature> signatureTable = new HashMap<String, AbstractSignature>();

	private final HashMap<BodyDecl, java.util.List<ExtendedSignature>> bodyMap = new HashMap<BodyDecl, java.util.List<ExtendedSignature>>();
	private final ArrayList<ExtendedSignature> originalList = new ArrayList<ExtendedSignature>();
	private final Hashtable<ExtendedSignature, ClassDecl> nonPrimitveTypesTable = new Hashtable<ExtendedSignature, ClassDecl>();

	private IMonitor monitor;

	public ProjectSignatures getProjectSignatures() {
		return projectSignatures;
	}

	public ExtendedFujiSignaturesJob(IFeatureProject featureProject) {
		this.featureProject = featureProject;
		projectSignatures = new ProjectSignatures(this.featureProject.getFeatureModel());
		featureDataConstructor = new FeatureDataConstructor(projectSignatures, FeatureDataConstructor.TYPE_FOP);
	}

	private AbstractSignature addFeatureID(AbstractSignature sig, int featureID, int startLine, int endLine) {
		SignatureReference sigRef = signatureSet.get(sig);
		if (sigRef == null) {
			sigRef = new SignatureReference(sig);
			signatureSet.put(sig, sigRef);
			signatureTable.put(sig.getFullName(), sig);
		}
		sigRef.addID((FOPFeatureData) featureDataConstructor.create(featureID, startLine, endLine));
		return sigRef.getSig();
	}

	private static String getClassPaths(IFeatureProject featureProject) {
		final StringBuilder classpath = new StringBuilder();
		final String sep = System.getProperty("path.separator");
		try {
			final JavaProject proj = new JavaProject(featureProject.getProject(), null);
			final IJavaElement[] elements = proj.getChildren();
			for (final IJavaElement e : elements) {
				final String path = e.getPath().toOSString();
				if (path.contains(":")) {
					classpath.append(sep);
					classpath.append(path);
					continue;
				}
				final IResource resource = e.getResource();
				if ((resource != null) && "jar".equals(resource.getFileExtension())) {
					classpath.append(sep);
					classpath.append(resource.getRawLocation().toOSString());
				}
			}
		} catch (final JavaModelException e) {

		}
		return classpath.length() > 0 ? classpath.substring(1) : classpath.toString();
	}

	private java.util.List<String> featureModulePathnames = null;

	@SuppressWarnings("rawtypes")
	private String getFeatureName(ASTNode astNode) {
		final int featureID = astNode.featureID();

		final String featurename = featureModulePathnames.get(featureID);
		return featurename.substring(featurename.lastIndexOf('\\') + 1);
	}

	@Override
	public ProjectSignatures execute(IMonitor monitor) throws Exception {
		this.monitor = monitor;
		final IFeatureModel fm = featureProject.getFeatureModel();
		fm.getAnalyser().setDependencies();

		final String sourcePath = featureProject.getSourcePath();
		final String[] fujiOptions = new String[] { "-" + Main.OptionName.CLASSPATH, getClassPaths(featureProject), "-" + Main.OptionName.PROG_MODE,
			"-" + Main.OptionName.COMPOSTION_STRATEGY, Main.OptionName.COMPOSTION_STRATEGY_ARG_FAMILY // "-typechecker",
			, "-" + Main.OptionName.BASEDIR, sourcePath };
		SPLStructure spl = null;
		Program ast;
		try {
			final Main fuji = new Main(fujiOptions, fm, FeatureUtils.extractConcreteFeaturesAsStringList(fm));

			final Composition composition = fuji.getComposition(fuji);
			ast = composition.composeAST();
			fuji.typecheckAST(ast);
			spl = fuji.getSPLStructure();
			featureModulePathnames = spl.getFeatureModulePathnames();
		} catch (final RuntimeException e) {
			throw e;
		} catch (final Exception e) {
			FeatureHouseCorePlugin.getDefault().logError(e);
			return null;
		}

		createSignatures(featureProject, ast);

		FeatureHouseCorePlugin.getDefault().logInfo(FUJI_SIGNATURES_LOADED_);
		return projectSignatures;
	}

	@SuppressWarnings("unchecked")
	private void createSignatures(IFeatureProject fp, Program ast) {
		int count = 0;
		final HashSet<String> packagesSet = new HashSet<>();

		Iterator<CompilationUnit> unitIter = ast.compilationUnitIterator();
		while (unitIter.hasNext()) {
			final CompilationUnit el = unitIter.next();
			if (el.featureID() >= 0) {
				++count;
				packagesSet.add(el.getPackageDecl());
			}
		}
		monitor.setRemainingWork(2 * count);

		final LinkedList<TypeDecl> stack = new LinkedList<TypeDecl>();
		final LinkedList<AbstractClassSignature> roleStack = new LinkedList<AbstractClassSignature>();

		unitIter = ast.compilationUnitIterator();
		while (unitIter.hasNext()) {
			final CompilationUnit unit = unitIter.next();
			if (unit.featureID() < 0) {
				continue;
			}
			String featurename = getFeatureName(unit);

			final List<TypeDecl> typeDeclList = unit.getTypeDeclList();
			final String pckg = unit.getPackageDecl();

			final List<ImportDecl> importList = unit.getImportDeclList();

			for (final TypeDecl rootTypeDecl : typeDeclList) {
				stack.push(rootTypeDecl);
				do {
					final TypeDecl typeDecl = stack.pop();
					String name = typeDecl.name();
					String modifierString = typeDecl.getModifiers().toString();
					String typeString = null;

					if (typeDecl instanceof ClassDecl) {
						typeString = "class";
					} else if (typeDecl instanceof InterfaceDecl) {
						typeString = "interface";
					}

					AbstractClassSignature parent = null;
					if (!roleStack.isEmpty()) {
						parent = roleStack.pop();
					}
					featurename = getFeatureName(typeDecl);
					int featureID = projectSignatures.getFeatureID(featurename);

					final FujiClassSignature curClassSig =
						(FujiClassSignature) addFeatureID(new FujiClassSignature(parent, name, modifierString, typeString, pckg, typeDecl, importList),
								featureID, Symbol.getLine(typeDecl.getStart()), Symbol.getLine(typeDecl.getEnd()));
					for (final ImportDecl importDecl : importList) {
						curClassSig.addImport(importDecl.toString());
					}

					for (final BodyDecl bodyDecl : typeDecl.getBodyDeclList()) {
						typeDecl.getModifiers();
						if (bodyDecl instanceof MethodDecl) {
							final MethodDecl method = (MethodDecl) bodyDecl;

							modifierString = method.getModifiers().toString();
							name = method.name();

							final TypeDecl type = method.type();

							final List<ParameterDeclaration> parameterList = method.getParameterList();
							final List<Access> exceptionList = method.getExceptionList();

							featurename = getFeatureName(bodyDecl);
							featureID = projectSignatures.getFeatureID(featurename);

							final AbstractSignature methAbs =
								addFeatureID(new FujiMethodSignature(curClassSig, name, modifierString, type, false, parameterList, exceptionList), featureID,
										Symbol.getLine(method.getStart()), Symbol.getLine(method.getEnd()));
							findMethodAccesses(method, methAbs, featureID);
						} else if (bodyDecl instanceof FieldDeclaration) {
							final FieldDeclaration field = (FieldDeclaration) bodyDecl;

							modifierString = field.getModifiers().toString();
							name = field.name();
							final TypeDecl type = field.type();

							featurename = getFeatureName(bodyDecl);
							featureID = projectSignatures.getFeatureID(featurename);

							addFeatureID(new FujiFieldSignature(curClassSig, name, modifierString, type), featureID, Symbol.getLine(field.getStart()),
									Symbol.getLine(field.getEnd()));

						} else if (bodyDecl instanceof ConstructorDecl) {
							final ConstructorDecl constructor = (ConstructorDecl) bodyDecl;
							if (!constructor.isDefaultConstructor()) {
								modifierString = constructor.getModifiers().toString();
								name = constructor.name();

								final TypeDecl type = constructor.type();

								final List<ParameterDeclaration> parameterList = constructor.getParameterList();
								final List<Access> exceptionList = constructor.getExceptionList();

								featurename = getFeatureName(bodyDecl);
								featureID = projectSignatures.getFeatureID(featurename);

								final AbstractSignature constrAbs =
									addFeatureID(new FujiMethodSignature(curClassSig, name, modifierString, type, true, parameterList, exceptionList),
											featureID, Symbol.getLine(constructor.getStart()), Symbol.getLine(constructor.getEnd()));
								findMethodAccesses(constructor, constrAbs, featureID);
							}

						} else if (bodyDecl instanceof MemberClassDecl) {
							stack.push(((MemberClassDecl) bodyDecl).getClassDecl());
							roleStack.push(curClassSig);
						} else if (bodyDecl instanceof MemberInterfaceDecl) {
							stack.push(((MemberInterfaceDecl) bodyDecl).getInterfaceDecl());
							roleStack.push(curClassSig);
						}
					}
				} while (!stack.isEmpty());
			}
			monitor.worked();
		}

		final AbstractSignature[] sigArray = new AbstractSignature[signatureSet.size()];
		int i = -1;

		for (final SignatureReference sigRef : signatureSet.values()) {
			final AbstractSignature sig = sigRef.getSig();
			sig.setFeatureData(sigRef.getFeatureData());
			sigArray[++i] = sig;
		}

		unitIter = ast.compilationUnitIterator();
		while (unitIter.hasNext()) {
			final CompilationUnit unit = unitIter.next();
			if (unit.featureID() < 0) {
				continue;
			}

			final List<TypeDecl> typeDeclList = unit.getTypeDeclList();
			final String pckg = unit.getPackageDecl();

			final List<ImportDecl> importList = unit.getImportDeclList();

			for (final TypeDecl rootTypeDecl : typeDeclList) {
				stack.push(rootTypeDecl);
				do {
					final TypeDecl typeDecl = stack.pop();
					String name = typeDecl.name();
					String modifierString = typeDecl.getModifiers().toString();
					String typeString = null;

					if (typeDecl instanceof ClassDecl) {
						typeString = "class";
					} else if (typeDecl instanceof InterfaceDecl) {
						typeString = "interface";
					}

					AbstractClassSignature parent = null;
					if (!roleStack.isEmpty()) {
						parent = roleStack.pop();
					}
					final FujiClassSignature curClassSig =
						(FujiClassSignature) signatureSet.get(new FujiClassSignature(parent, name, modifierString, typeString, pckg, typeDecl, importList)).sig;

					for (final BodyDecl bodyDecl : typeDecl.getBodyDeclList()) {
						typeDecl.getModifiers();
						final java.util.List<ExtendedSignature> accessingSignatures = bodyMap.remove(bodyDecl);
						if (accessingSignatures != null) {
							SignatureReference sigRef = null;
							if (bodyDecl instanceof MethodDecl) {
								final MethodDecl method = (MethodDecl) bodyDecl;
								modifierString = method.getModifiers().toString();
								name = method.name();

								final TypeDecl type = method.type();

								final List<ParameterDeclaration> parameterList = method.getParameterList();
								final List<Access> exceptionList = method.getExceptionList();
								sigRef =
									signatureSet.get(new FujiMethodSignature(curClassSig, name, modifierString, type, false, parameterList, exceptionList));
							} else if (bodyDecl instanceof FieldDeclaration) {
								final FieldDeclaration field = (FieldDeclaration) bodyDecl;

								modifierString = field.getModifiers().toString();
								name = field.name();
								final TypeDecl type = field.type();

								sigRef = signatureSet.get(new FujiFieldSignature(curClassSig, name, modifierString, type));
							} else if (bodyDecl instanceof ConstructorDecl) {
								final ConstructorDecl constructor = (ConstructorDecl) bodyDecl;
								if (!constructor.isDefaultConstructor()) {
									modifierString = constructor.getModifiers().toString();
									name = constructor.name();
									final TypeDecl type = constructor.type();

									final List<ParameterDeclaration> parameterList = constructor.getParameterList();
									final List<Access> exceptionList = constructor.getExceptionList();

									sigRef =
										signatureSet.get(new FujiMethodSignature(curClassSig, name, modifierString, type, true, parameterList, exceptionList));
								}
							}
							if (sigRef != null) {
								for (final ExtendedSignature absSig : accessingSignatures) {
									final FOPFeatureData[] featureData = (FOPFeatureData[]) absSig.sig.getFeatureData();
									for (int j = 0; j < featureData.length; j++) {
										if (featureData[j].getID() == absSig.featureID) {
											featureData[j].addCalledSignature(sigRef.sig);
											break;
										}
									}
								}
							}
						} else if (bodyDecl instanceof MemberClassDecl) {
							stack.push(((MemberClassDecl) bodyDecl).getClassDecl());
							roleStack.push(curClassSig);
						}
					}
				} while (!stack.isEmpty());
			}
			monitor.worked();
		}
		for (final ExtendedSignature extSig : originalList) {
			final FOPFeatureData[] featureData = (FOPFeatureData[]) extSig.sig.getFeatureData();
			for (int j = 0; j < featureData.length; j++) {
				if (featureData[j].getID() == extSig.featureID) {
					featureData[j].setUsesOriginal(true);
					break;
				}
			}

		}

		for (final Entry<ExtendedSignature, ClassDecl> extSig : nonPrimitveTypesTable.entrySet()) {
			final FOPFeatureData[] featureData = (FOPFeatureData[]) extSig.getKey().sig.getFeatureData();
			for (int j = 0; j < featureData.length; j++) {
				if ((featureData[j].getID() == extSig.getKey().featureID) && packagesSet.contains(extSig.getValue().compilationUnit().getPackageDecl())) {
					final ClassDecl value = extSig.getValue();
					featureData[j].addUsedNonPrimitveType(value.compilationUnit().getPackageDecl() + "." + value.name());
					break;
				}
			}
		}

		for (final java.util.List<ExtendedSignature> value : bodyMap.values()) {
			for (final ExtendedSignature absSig : value) {
				if (absSig.sig instanceof AbstractMethodSignature) {
					final AbstractMethodSignature methSig = (AbstractMethodSignature) absSig.sig;
					if (methSig.isConstructor()) {
						continue;
					}
				}
				final FOPFeatureData[] featureData = (FOPFeatureData[]) absSig.sig.getFeatureData();
				for (int j = 0; j < featureData.length; j++) {
					if (featureData[j].getID() == absSig.featureID) {
						featureData[j].setUsesExternMethods(true);
						break;
					}
				}
			}
		}

		fp.getComposer().buildFSTModel();
		final FSTModel fst = fp.getFSTModel();

		if (fst == null) {
			FeatureHouseCorePlugin.getDefault().logInfo("No FSTModel provided.");
		} else {
			for (final FSTFeature fstFeature : fst.getFeatures()) {
				final int id = projectSignatures.getFeatureID(fstFeature.getName());

				for (final FSTRole fstRole : fstFeature.getRoles()) {
					final FSTClassFragment classFragment = fstRole.getClassFragment();
					String fullName = (classFragment.getPackage() == null ? "" : classFragment.getPackage()) + "." + classFragment.getName();
					if (fullName.endsWith(".java")) {
						fullName = fullName.substring(0, fullName.length() - ".java".length());
					}
					copyComment_rec(classFragment, id, fullName);
				}
			}
		}

		projectSignatures.setSignatureArray(sigArray);
		featureProject.getFSTModel().setProjectSignatures(projectSignatures);
	}

	private void findMethodAccesses(ASTNode<?> stmt, AbstractSignature methAbs, int featureID) {
		if (stmt == null) {
			return;
		}

		if (stmt instanceof MethodAccess) {
			if ("original".equals(((MethodAccess) stmt).name())) {
				originalList.add(new ExtendedSignature(methAbs, featureID));
			} else {
				putAccess(((MethodAccess) stmt).decl(), methAbs, featureID);
			}
			for (int i = 0; i < stmt.getNumChildNoTransform(); i++) {
				findMethodAccesses(stmt.getChildNoTransform(i), methAbs, featureID);
			}
		} else if (stmt instanceof ConstructorAccess) {
			putAccess(((ConstructorAccess) stmt).decl(), methAbs, featureID);
		} else if (stmt instanceof VarAccess) {
			final Iterator<?> declIt = ((VarAccess) stmt).decls().iterator();
			while (declIt.hasNext()) {
				final Object fieldDecl = declIt.next();
				if (fieldDecl instanceof FieldDeclaration) {
					putAccess((FieldDeclaration) fieldDecl, methAbs, featureID);
					break;
				}
			}
		} else if (stmt instanceof ClassInstanceExpr) {
			final Iterator<?> iterator = (((ClassInstanceExpr) stmt).decls().iterator());
			while (iterator.hasNext()) {
				final Object cur = iterator.next();
				if (cur instanceof ConstructorDecl) {
					putAccess((ConstructorDecl) cur, methAbs, featureID);
					break;
				}
			}
		} else if (stmt instanceof TypeAccess) {
			final Iterator<?> iterator = (((TypeAccess) stmt).decls().iterator());
			while (iterator.hasNext()) {
				final Object cur = iterator.next();
				if (cur instanceof ClassDecl) {
					nonPrimitveTypesTable.put(new ExtendedSignature(methAbs, featureID), (ClassDecl) cur);
					break;
				}
			}
		} else {
			for (int i = 0; i < stmt.getNumChildNoTransform(); i++) {
				findMethodAccesses(stmt.getChildNoTransform(i), methAbs, featureID);
			}
		}
	}

	private void putAccess(BodyDecl typeDecl, AbstractSignature methAbs, int featureID) {
		java.util.List<ExtendedSignature> signatureList = bodyMap.get(typeDecl);
		if (signatureList == null) {
			signatureList = new LinkedList<ExtendedSignature>();
			bodyMap.put(typeDecl, signatureList);
		}
		signatureList.add(new ExtendedSignature(methAbs, featureID));
	}

	private void copyComment(IRoleElement element, int id, String fullName) {
		if (fullName == null) {
			return;
		}
		final AbstractSignature sig = signatureTable.get(fullName);

		if (sig != null) {
			final FOPFeatureData[] ids = (FOPFeatureData[]) sig.getFeatureData();
			for (int j = 0; j < ids.length; j++) {
				final FOPFeatureData featureData = ids[j];
				if (featureData.getID() == id) {
					featureData.setComment(element.getJavaDocComment());
					break;
				}
			}
		}
	}

	private void copyComment_rec(FSTClassFragment classFragment, int id, String fullName) {
		copyComment(classFragment, id, fullName);
		for (final FSTField field : classFragment.getFields()) {
			copyComment(field, id, fullName + "." + field.getName());
		}
		for (final FSTMethod method : classFragment.getMethods()) {
			copyComment(method, id, fullName + "." + method.getName());
		}
		for (final FSTClassFragment innerClasses : classFragment.getInnerClasses()) {
			copyComment_rec(innerClasses, id, fullName + "." + innerClasses.getName());
		}
	}
}
