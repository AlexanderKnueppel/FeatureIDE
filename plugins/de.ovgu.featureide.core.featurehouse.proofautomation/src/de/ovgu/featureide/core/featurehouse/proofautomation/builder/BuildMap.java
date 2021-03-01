/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.core.featurehouse.proofautomation.builder;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;


import org.eclipse.core.resources.IProject;
import org.stringtemplate.v4.compiler.STParser.mapExpr_return;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;

import bibliothek.extension.gui.dock.preference.preferences.choice.DefaultChoice.Entry;
import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.featurehouse.proofautomation.evaluation.SingleApproachEvaluation;
import de.ovgu.featureide.core.featurehouse.proofautomation.filemanagement.FileManager;
import de.ovgu.featureide.core.featurehouse.proofautomation.model.FillMethodMap;
import de.ovgu.featureide.core.featurehouse.proofautomation.model.Method;
import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.base.FOPFeatureData;
import de.ovgu.featureide.core.signature.filter.MethodFilter;
import de.ovgu.featureide.featurehouse.FeatureHouseCorePlugin;
import de.ovgu.featureide.featurehouse.meta.featuremodel.FeatureModelClassGenerator;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelStructure;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;

/**
 * Fills the Methodmap for alls method information from the featuremodel (only use before start of JVM)
 * 
 * @author Marlen Herter-Bernier
 */
public class BuildMap {

	protected static final String FILE_SEPERATOR = System.getProperty("file.separator");
	public void main(String[] args) {
		Map<String, Map<String, Method>> methodMap = new HashMap<>();
		File projectDir = new File("/mnt/54AFF99F466B2AED/Informatik/Masterarbeit/eval2/Sandbox/BankAccountv1");
		// parseMethodsInMetaproduct(projectDir, methodMap);
		// parseMethodsFromFeatureModel(projectDir, methodMap);
	}



	/**
	 * run through the Featuremodel of the project to get all method information
	 * 
	 * @param project
	 * @param projectVersions
	 */
	public static void parseMethodsFromFeatureModel(IProject project, List<SingleApproachEvaluation> projectVersions) {
		if (project != null) {
			SingleApproachEvaluation singleApproachEvaluation = getSingleProject(project, projectVersions);
			Map<String, Map<String, Method>> methodMap = new HashMap<String, Map<String, Method>>();
			if (singleApproachEvaluation != null) {
				final IFeatureProject featureProject = CorePlugin.getFeatureProject(project);
				FSTModel fstModel = featureProject.getFSTModel();
				for (FSTClass clazz : fstModel.getClasses()) {
					if (!clazz.getName().equals("Main.java")) {
						methodMap.put(clazz.getName().replace(".java", ""),
								new HashMap<String, Method>());
					}
				}
				ProjectSignatures signatures = fstModel.getProjectSignatures();
				// String rootFeature = fmodel.getStructure().getRoot().getFeature().getName();
				final LinkedList<FSTFeature> features = new LinkedList<FSTFeature>(
						featureProject.getFSTModel().getFeatures());
				while (!features.isEmpty()) {
					FSTFeature fstFeat;
					while (!(fstFeat = features.removeFirst()).hasMethodContracts()) {
					}
					;

					fillMap(fstFeat, signatures, methodMap);
				}
				//FillMethodMap.printMap(methodMap);
			}
			File csvFile = new File(
					singleApproachEvaluation.evaluatePath.getAbsolutePath() + FILE_SEPERATOR + "methodMap.csv");
			writeMapToCSV(methodMap, csvFile);

		}

	}

	/**
	 * 
	 * @param feat
	 * @param signatures
	 * @param singleApproachEvaluation
	 */
	private static void fillMap(final FSTFeature feat, final ProjectSignatures signatures,
			Map<String, Map<String, Method>> methodMap) {
		Thread keyThread = new Thread() {
			@SuppressWarnings("restriction")
			public void run() {
				int featureID = signatures.getFeatureID(feat.getName());
				for (FSTRole role : feat.getRoles()) {
					final String roleName = role.getClassFragment().getName();
					if (roleName.equals("Main.java")) {
						continue;
					}

					TreeSet<FSTField> set = role.getClassFragment().getFields();
					for (FSTMethod meth : role.getClassFragment().getMethods()) {
						final SignatureIterator sigIterator = signatures.iterator();
						sigIterator.addFilter(new MethodFilter());
						
						while (sigIterator.hasNext()) {
							AbstractSignature curSig = sigIterator.next();
							for (int i = 0; i < curSig.getFeatureData().length; i++) {
								if ((curSig.getFeatureData())[i].getID() == featureID
										&& curSig.getName().equals(meth.getName())
										&& curSig.getFeatureData()[i].getStartLineNumber() == meth.getLine()) {
									final FOPFeatureData fopFeatureData = ((FOPFeatureData[]) curSig
											.getFeatureData())[i];
									Method method = new Method();
									method.setName(meth.getName());
									method.setFeature(role.getFeature().getName());
									method.setRootFeature(
											signatures.getFeatureModel().getStructure().getRoot().getFeature().getName());
									
									List<AbstractSignature> calledSig = fopFeatureData.getCalledSignatures();

									if (fopFeatureData.usesOriginal()) {
										if(curSig.getFeatureData().length >= i+1) {
											method.setOriginal(curSig.getFeatureData()[i+1].getConstraint().toString());
											method.setName(meth.getName() + "_" + method.getFeature());
										}
									}
									List<String> calledMethodsList = new ArrayList<String>();
									List<String> parameterList = new ArrayList<String>();
									List<String> fieldList = new ArrayList<String>();
									// all parameters of the method
									for (String p : curSig.getParameterList()) {
										parameterList.add(p);
									}
									for (AbstractSignature called : calledSig) {
										String parameter = called.getName();
										// check if the parameter belongs to the same class. if not, add class to name
										if (!called.getParent().equals(curSig.getParent())) {
											parameter = called.getParent().getName().toLowerCase() + "." + parameter;
										}
										// if signature is a Method put it into calledMethodslist
										if (called.getClass().getSimpleName().equals("FujiMethodSignature")
												&& !calledMethodsList.contains(parameter)) {
											calledMethodsList.add(parameter);
											continue;
										}
										// if a field is used in the signatures add it to fieldlist
										for (FSTField field : set) {
											if (field.getName().equals(parameter)
													&& !fieldList.contains(field.getName())) {
												fieldList.add(field.getName());
											}
										}
										// if parameter is not already in one of the lists and is not a class, add it to
										// parameterlist
										if (!parameterList.contains(called.getType() + " " + parameter)
												&& !fieldList.contains(parameter)
												&& !calledMethodsList.contains(parameter) && !methodMap.containsKey(called.getType())) {
											parameterList.add(called.getType() + " " + parameter);
										}
									}
									//System.out.println(method.getName());
									method.setFields(fieldList);
									method.setParameter(parameterList);
									method.setCalledMethod(calledMethodsList);
									methodMap.get(roleName.replace(".java", "")).put(method.getName(),
											method);
								}
							}
						}
						
					}

				}
			}
		};
		keyThread.start();
		try {
			keyThread.join();
		} catch (InterruptedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	/**
	 * 
	 * @param project
	 * @param projectVersions
	 * @return
	 */
	private static SingleApproachEvaluation getSingleProject(IProject project,
			List<SingleApproachEvaluation> projectVersions) {
		for (SingleApproachEvaluation s : projectVersions) {
			if (s.toEvaluate.getName().equals(project.getName())) {
				return s;
			}
		}
		return null;
	}

	public static void writeMapToCSV(Map<String, Map<String, Method>> methodMap, File csvFile) {
		try {
			FileWriter myWriter = new FileWriter(csvFile);
			Iterator<String> it = methodMap.keySet().iterator();
			String writing= "";
			while (it.hasNext())
			{
				String key = it.next();
				Map<String, Method> innerMethodMap = methodMap.get(key);
				Iterator<String> innerIt = innerMethodMap.keySet().iterator();
				while(innerIt.hasNext()) {
					String methodName = innerIt.next();
					Method method = methodMap.get(key).get(methodName);

					String parameterString = "";
					String fieldString = "";
					String calledString = "";
					for (String p : method.getParameter()) {
						parameterString = p + "," + parameterString;
					}
					if (!parameterString.isEmpty())
						parameterString = parameterString.substring(0, parameterString.length() - 1);
					for (String f : method.getFields()) {
						fieldString = f + "," + fieldString;
					}
					if (!fieldString.isEmpty())
						fieldString = fieldString.substring(0, fieldString.length() - 1);
					for (String c : method.getCalledMethod()) {
						calledString = c + "," + calledString;
					}
					if (!calledString.isEmpty())
						calledString = calledString.substring(0, calledString.length() - 1);

					writing = writing+("\"" + key + "\";\"" + method.getName() + "\";\"" + parameterString + "\";\""
							+ fieldString + "\";\"" + calledString + "\";\"" + method.getOriginal() + "\";\""
							+ method.getRootFeature() + "\";\"" + method.getFeature() + "\"\n");
				}
			}myWriter.write(writing);
			myWriter.close();
		} catch (IOException e) {
			System.out.println("An error occurredw writing the csv-File");
			e.printStackTrace();
		}
	}

	// -------------Java-Parser-Part------------------

	/**
	 * parse the Metaproduct Java files into a the map
	 * 
	 * @param projectDir
	 * @param recordMap
	 */
	public static void parseMethodsInMetaproduct(File projectDir, Map<String, Map<String, Method>> methodMap) {

		File[] metaproduct = (new File(projectDir.getAbsolutePath() + FILE_SEPERATOR + FileManager.metaproductDir))
				.listFiles();
		for (File clazz : metaproduct) {
			if (clazz.getName().endsWith(".java")) {
				String className = clazz.getName().substring(0, clazz.getName().indexOf(".java"));
				JavaParser javaParser = new JavaParser();
				try {
					ParseResult<CompilationUnit> existingCompilationUnitParse = javaParser.parse(clazz);

					methodMap.put(className, new HashMap<String, Method>());
					if (existingCompilationUnitParse.isSuccessful()
							&& existingCompilationUnitParse.getResult().isPresent()) {

						CompilationUnit compilationUnit = existingCompilationUnitParse.getResult().get();
						List<String> fieldList = new ArrayList<>();
						compilationUnit.findAll(FieldDeclaration.class).forEach(field -> {
							field.getVariables().forEach(variable -> {
								if (variable.getType().isClassOrInterfaceType()) {
									fieldList.add(variable.getNameAsString() + ".");
								} else {
									System.out.println("Field name: " + variable.getName().asString());
									fieldList.add(variable.getNameAsString());
								}
							});
						});
						compilationUnit.findAll(MethodDeclaration.class).forEach(methodD -> {
							System.out.println("Method name: " + methodD.getNameAsString());
							String methodName = methodD.getNameAsString();
							Method method = new Method();
							method.setName(methodName);

							List<String> parameters = new ArrayList<String>();
							for (int i = 0; i < methodD.getParameters().size(); i++) {
								String parameter = methodD.getParameters().get(i).toString().split(" ")[1];
								parameters.add(parameter);
								System.out.println("Parameter name: " + parameter);
							}
							if (!parameters.isEmpty()) {
								method.setParameter(parameters);
							}
							// search for used fields in method
							List<String> usedFields = new ArrayList<>();
							methodD.getBody().get().getStatements().forEach(stmt -> {
								stmt.getChildNodes().forEach(var -> {
									nodeIterator(var, usedFields, fieldList);
								});
							});
							if (!usedFields.isEmpty()) {
								method.setFields(usedFields);
							}
							methodMap.get(className).put(methodName, method);
						});

					}
				} catch (FileNotFoundException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
		}

	}

	static void nodeIterator(Node node, List<String> usedFields, List<String> fieldList) {
		node.getChildNodes().forEach(var -> {
			fieldList.forEach(field -> {
				if (field.endsWith(".")) {
					field = field.replace(".", "");
					final String regex = "(" + field + "\\.\\w+)";
					final Pattern pattern = Pattern.compile(regex);
					final Matcher matcher = pattern.matcher(var.toString());

					// if field matches regex
					if (matcher.matches()) {
						// get the last group -> the fieldName
						final String name = matcher.group(matcher.groupCount());

						if (!usedFields.contains(name)) {
							System.out.println("FieldName: " + name);
							usedFields.add(name);
						}
					}
				} else if (var.toString().equals(field) && !usedFields.contains(field)) {
					System.out.println("FieldName: " + var);
					usedFields.add(field);
				}
			});
			nodeIterator(var, usedFields, fieldList);
		});
	}
}
