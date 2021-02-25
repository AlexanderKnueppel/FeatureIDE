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
package de.ovgu.featureide.core.featurehouse.proofautomation.key;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.stream.Collector;
import java.util.stream.Collectors;

import org.antlr.grammar.v3.TreeToNFAConverter.set_return;
import org.key_project.util.collection.ImmutableList;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.featurehouse.proofautomation.builder.BuilderUtil;
import de.ovgu.featureide.core.featurehouse.proofautomation.filemanagement.FileManager;
import de.ovgu.featureide.core.featurehouse.proofautomation.model.Method;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.recoderext.adt.MethodSignature;
import de.uka.ilkd.key.logic.IntIterator;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.macros.AutoMacro;
import de.uka.ilkd.key.macros.FullAutoPilotProofMacro;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.BuiltInRuleAppIndex;
import de.uka.ilkd.key.proof.BuiltInRuleIndex;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.JavaModel;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.strategy.Strategy;

import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.util.MiscTools;

/**
 * TODO description
 * 
 * @author Marlen Herter-Bernier
 */
public class Non_Rigid extends KeyHandler {
	public static String FILE_SEPERATOR = System.getProperty("file.separator");
	private static String[] jml = { "combination", "originalFrame", "originalPre", "originalPost" };
	private KeYEnvironment<?> keYEnvironment;

	private static Map<String, Map<String, Record>> recordMap = new HashMap<>();
	private static Map<String, Map<String, Method>> methodMap = new HashMap<>();

	/**
	 * Initializes the abstract execution proof
	 * 
	 * @param oldPartialProof
	 * @param maxRuleApplication
	 * @param defaultSettingsForFeatureStub
	 */
	public void startAbstractProof(ProofHandler proofHandler, int maxRuleApplication, StrategyProperties sp) {
		KeYEnvironment<?> environment = proofHandler.getEnvironment();
		Contract contract = proofHandler.getContract();

		try {

			ProofOblInput input = contract.createProofObl(environment.getInitConfig(), contract);
			proofHandler.proof = environment.createProof(input);

			// Set proof strategy options
			ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
			HashMap<String, String> choices = proofHandler.proof.getSettings().getChoiceSettings().getDefaultChoices();
			choices.putAll(MiscTools.getDefaultTacletOptions());
			choiceSettings.setDefaultChoices(choices);

			proofHandler.proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
			ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(maxRuleApplication);
			ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(sp);
			proofHandler.proof.getSettings().getStrategySettings().setMaxSteps(maxRuleApplication);
			proofHandler.proof.setActiveStrategy(proofHandler.proof.getServices().getProfile()
					.getDefaultStrategyFactory().create(proofHandler.proof, sp));

			ProofControl proofControl = environment.getProofControl();
			int previousNodes;
			do {
				previousNodes = proofHandler.proof.countNodes();

				proofControl.startAndWaitForAutoMode(proofHandler.proof);

			} while (proofHandler.proof.countNodes() == previousNodes);
			if (proofHandler.proof.openGoals().isEmpty()) {
				System.out.println("Proof " + proofHandler.proof.name() + " was closed");
				proofHandler.setClosed(true);
			}
			proofHandler.setStatistics();
			environment.dispose();
		} catch (ProofInputException e) {
			System.out.println("Exception at '" + contract.getDisplayName() + "' of " + contract.getTarget() + ":");
			e.printStackTrace();
		}
	}

	public boolean startMetaProductProof(ProofHandler proofHandler, File reuseProof, StrategyProperties sp,
			int maxRuleApplication, String savePath, Map<String, Map<String, Record>> rMap,
			Map<String, Map<String, Method>> mMap) {
		recordMap = rMap;
		methodMap = mMap;
		UserInterfaceControl userInterface = new DefaultUserInterfaceControl(null);
		boolean reusedAProof = true;

		System.out.println("Reuse proof: " + reuseProof.getName());

		try {
			AbstractProblemLoader loader = userInterface.load(null, reuseProof, null, null, null, sp, false);
			InitConfig initConfig = loader.getInitConfig();
			keYEnvironment = new KeYEnvironment<>(userInterface, initConfig, loader.getProof(), loader.getProofScript(),
					loader.getResult());
			Services services = keYEnvironment.getServices();
			proofHandler.proof = keYEnvironment.getLoadedProof();
			ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
			HashMap<String, String> choices = new HashMap<String, String>();
			choices.put("assertions", "assertions:safe");
			choices.putAll(MiscTools.getDefaultTacletOptions());
			choiceSettings.setDefaultChoices(choices);

			ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(maxRuleApplication);
			ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(sp);
			proofHandler.proof.getSettings().getStrategySettings().setMaxSteps(maxRuleApplication);
			proofHandler.proof.setActiveStrategy(
					keYEnvironment.getProfile().getDefaultStrategyFactory().create(proofHandler.proof, sp));

			String methodName = proofHandler.getTargetName();
			if (!methodName.equals("<inv>")) {
				methodName = methodName.split("\\(")[0];
			}

			System.out.println("Starte proof of  " + proofHandler.proof.name());
			proofHandler.setReusedStatistics();

			System.out.println("Reused: " + proofHandler.getTargetName() + "\n" + proofHandler.proof.getStatistics());
			if (!proofHandler.proof.openGoals().isEmpty()) {
				keYEnvironment.getProofControl().startAndWaitForAutoMode(proofHandler.proof);
				// overwrite the other statistic of the goal-proof because they did not close
				proofHandler.setStatistics();
				System.out.println(proofHandler.getTargetName() + "was Closed with first startAndWaitForAutoMode ?: "
						+ proofHandler.proof.closed() + "\n" + proofHandler.proof.getStatistics());
			}
			if (!proofHandler.proof.openGoals().isEmpty()) {

				/*for (Goal goal : proofHandler.proof.openGoals()) {
					changeRecord(proofHandler.getTypeName(), methodName);
					addInformationToGoal(methodName, proofHandler.getTypeName(), services, goal);

					// create new Proof with goal as root
					
					 * InitConfig config = proofHandler.proof.getInitConfig().deepCopy();
					 * 
					 * Proof proof = new Proof(proofHandler.proof.name().toString(), goal.sequent(),
					 * proofHandler.proof.header(), config.createTacletIndex(),
					 * config.createBuiltInRuleIndex(), config); int nrNodes = proof.countNodes();
					 * ProofControl proofControl = keYEnvironment.getProofControl();
					 * FullAutoPilotProofMacro fappm = new FullAutoPilotProofMacro(); // run the
					 * marco and than the proofing proofControl.runMacro(proof.root(), fappm, null);
					 * proofControl.waitWhileAutoMode();
					 * keYEnvironment.getProofControl().startAndWaitForAutoMode(proof);
					 * System.out.println("Goal " + i + " with new Proof " + proof.name().toString()
					 * + " was Closed?: " + proof.closed() + " \n" + proof.getStatistics());
					 * proofHandler.addProofStatistic(proof);
					 * 
					 * int recursionNr = 1; if (proof.closed()) {
					 * proofHandler.proof.closeGoal(goal); } else if (nrNodes < proof.countNodes()
					 * && !proof.closed()) { System.out.println(goal.toString());
					 * proofHandler.addProofStatistic(proof); proovingWithRecursion(proof,
					 * proofHandler.getTypeName(), proofHandler.proof.getInitConfig(), goal, i,
					 * recursionNr, proofHandler); if (proof.closed()) {
					 * proofHandler.proof.closeGoal(goal); } } else { proovingWithRecursion(proof,
					 * proofHandler.getTypeName(), proofHandler.proof.getInitConfig(), goal, i,
					 * recursionNr, proofHandler); if (proof.closed()) {
					 * proofHandler.proof.closeGoal(goal); } } i++;
					 
				}*/
				reusedAProof = true;
				/*
				 * if (!proofHandler.proof.openGoals().isEmpty()) {
				 * keYEnvironment.getProofControl().startAndWaitForAutoMode(proofHandler.proof);
				 * // overwrite the other statistic of the goal-proof because they did not close
				 * proofHandler.setStatistics(); System.out.println(proofHandler.getTargetName()
				 * + "was Closed with startAndWaitForAutoMode second time?: " +
				 * proofHandler.proof.closed()); }
				 */
				int count = 0;
				while (!proofHandler.proof.openGoals().isEmpty() && count < 20) {
					for (Goal goal : proofHandler.proof.openGoals()) {
						changeRecord(proofHandler.getTypeName(), methodName);
						addInformationToGoal(methodName, proofHandler.getTypeName(), services, goal);
					}
					int previousNodes = proofHandler.proof.countNodes();

					keYEnvironment.getProofControl().startAndWaitForAutoMode(proofHandler.proof);
					count++;
					System.out.println("Open goals " + proofHandler.proof.openGoals().size() + " open Goals");
					System.out.println(
							proofHandler.getTargetName() + "was Closed with startAndWaitForAutoMode second time?: "
									+ proofHandler.proof.closed() + "\n Nodes:" + proofHandler.proof.countNodes());
					if (proofHandler.proof.countNodes() - previousNodes < 5) {
						break;
					}
				}
			}
			if (proofHandler.proof.openGoals().isEmpty()) {
				System.out.println("Metaproductproof of " + proofHandler.getTargetName() + " in "
						+ proofHandler.getTypeName() + " was closed");
				proofHandler.setClosed(true);
			}
		} catch (ProblemLoaderException e) {
			System.out.println("Exception at '" + proofHandler.getTargetName() + ":");
			throw new RuntimeException(e);
		}
		System.out.println(
				"Final Statistic: " + proofHandler.getTargetName() + "\n" + proofHandler.proof.getStatistics());

		return reusedAProof;
	}

	/**
	 * 
	 * @param proofHandler
	 * @param oldPartialProof
	 * @param savePath
	 * @param maxRuleApplication
	 * @param defaultSettingsForFeatureStub
	 */
	public void replayFeatureStubProof(ProofHandler proofHandler, File oldPartialProof, String savePath,
			int maxRuleApplication, StrategyProperties defaultSettingsForFeatureStub) {
		System.out.println("Start replayFeatureStubProof of target: " + proofHandler.getTargetName());
		boolean reusedAProof = false;
		System.out.println(oldPartialProof.getAbsolutePath());
		try {
			KeYEnvironment<?> keYEnvironment = proofHandler.getEnvironment();
			Contract contract = proofHandler.getContract();
			ProofOblInput input = contract.createProofObl(keYEnvironment.getInitConfig(), contract);

			proofHandler.proof = keYEnvironment.createProof(input);
			HashMap<String, String> choices = proofHandler.proof.getSettings().getChoiceSettings().getDefaultChoices();
			choices.put("assertions", "assertions:safe");
			ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
			choiceSettings.setDefaultChoices(choices);

			if (oldPartialProof != null) {
				if (oldPartialProof.getName().endsWith(".proof")) {
					UserInterfaceControl userInterface = new DefaultUserInterfaceControl(null);
					try {

						AbstractProblemLoader loader = userInterface.load(null, oldPartialProof, null, null, null, null,
								false);
						InitConfig initConfig = loader.getInitConfig();
						keYEnvironment = new KeYEnvironment<>(userInterface, initConfig, loader.getProof(),
								loader.getProofScript(), loader.getResult());
						proofHandler.proof = keYEnvironment.getLoadedProof();
						String methodName = proofHandler.getTargetName();
						if (!methodName.equals("<inv>")) {
							methodName = methodName.split("\\(")[0];
						}
						for (Goal goal : proofHandler.proof.openGoals()) {
							changeRecord(proofHandler.getTypeName(), methodName);
							addInformationToGoal(methodName, proofHandler.getTypeName(), keYEnvironment.getServices(),
									goal);
						}
						ProofControl proofControl = keYEnvironment.getProofControl();

						proofControl.startAndWaitForAutoMode(proofHandler.proof);
						reusedAProof = true;

					} catch (ProblemLoaderException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
					// savePath = oldPartialProof.getParentFile().getAbsolutePath();
					File reusedProof = proofHandler.saveProof(savePath);
					try {
						replaceJavaSource(reusedProof);
						keYEnvironment.load(reusedProof);
						proofHandler.setProof(keYEnvironment.getLoadedProof());
					} catch (ProblemLoaderException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
					reusedProof.delete();
					proofHandler.setReusedStatistics();
					// keYEnvironment.dispose();
				}
			}
		} catch (Exception e) {
			e.printStackTrace();
		}

	}

	/**
	 * 
	 * @param proof
	 * @param reuseProof
	 * @param services
	 * @param goal
	 * @param oldgoal
	 * @param oldContractMap
	 * @return
	 */
	private void addInformationToGoal(String methodName, String className, Services services, Goal goal) {
		SequentFormula cf;
		TermBuilder termBuilder = services.getTermBuilder();
		int seqSize = goal.sequent().size();

		Record record = recordMap.get(className).get(methodName);
		if (record == null) {
			return;
		}
		if (!record.isPrepared()) {
			changeRecord(className, methodName);
			record = recordMap.get(className).get(methodName);
		}
		try {
			if (record != null) {

				for (int j = 1; j <= seqSize; j++) {
					PosInOccurrence posInOccurrence = PosInOccurrence.findInSequent(goal.sequent(), j,
							PosInTerm.getTopLevel());
					String sequent = goal.sequent().getFormulabyNr(j).toString();
					// System.out.println(sequent);
					if (sequent.contains("OriginalPre<<origin") && record.getOriginalPre() != "") {
						if (posInOccurrence.isInAntec()) {
							System.out.println("OriginalPre: " + record.getOriginalPre());
							cf = new SequentFormula(termBuilder.parseTerm(
									"OriginalPre <->(" + record.getOriginalPre() + ")", goal.getLocalNamespaces()));
							goal.addFormula(cf, true, false);
							seqSize = goal.sequent().size();
						} else {
							String originalpre = getOtherOriginalPreString(record, className, methodName);
							if (!originalpre.isEmpty()) {
								System.out.println("OriginalPre part 2: " + originalpre);
								cf = new SequentFormula(termBuilder.parseTerm("OriginalPre <->" + originalpre,
										goal.getLocalNamespaces()));
								goal.addFormula(cf, false, false);
								seqSize = goal.sequent().size();
							}
						}
					}
					if (sequent.contains("OriginalPost<<origin") && record.getOriginalPost() != "") {
						if (posInOccurrence.isInAntec()) {
							System.out.println("OriginalPost: " + record.getOriginalPost());
							cf = new SequentFormula(termBuilder.parseTerm(
									"OriginalPost <-> (" + record.getOriginalPost() + ")", goal.getLocalNamespaces()));
							goal.addFormula(cf, true, false);
							seqSize = goal.sequent().size();
						} else {
							String originalpost = getOtherOriginalPreString(record, className, methodName);
							if (!originalpost.isEmpty()) {
								System.out.println("OriginalPost part 2: " + originalpost);
								cf = new SequentFormula(termBuilder.parseTerm("OriginalPost <->" + originalpost,
										goal.getLocalNamespaces()));
								goal.addFormula(cf, false, false);
								seqSize = goal.sequent().size();
							}
						}
					}

					if (sequent.contains("OriginalFrame<<origin") && !record.getOriginalFrame().isEmpty()) {
						if (posInOccurrence.isInAntec()) {
							System.out.println("OriginalFrame: " + record.getOriginalFrame());
							cf = new SequentFormula(
									termBuilder.parseTerm(record.getOriginalFrame(), goal.getLocalNamespaces()));
							goal.addFormula(cf, true, false);
							seqSize = goal.sequent().size();
						} else {
							String originalframe = getOtherOriginalPreString(record, className, methodName);
							if (!originalframe.isEmpty()) {
								System.out.println("OriginalFrame part 2: " + originalframe);
								cf = new SequentFormula(termBuilder.parseTerm("OriginalFrame: " + originalframe,
										goal.getLocalNamespaces()));
								goal.addFormula(cf, false, false);
								seqSize = goal.sequent().size();
							}
						}
					}

					if (sequent.contains("AllowedFeatureCombination<<origin") && !record.getCombination().isEmpty()) {
						if (posInOccurrence.isInAntec()) {
							System.out.println("AllowedFeatureCombination: " + record.getCombination());
							cf = new SequentFormula(
									termBuilder.parseTerm("" + record.getCombination(), goal.getLocalNamespaces()));
							goal.removeFormula(posInOccurrence);
							goal.addFormula(cf, true, false);
							seqSize = goal.sequent().size();
						} else {
							String combination = getCombinationString(record, className, methodName);
							if (!combination.isEmpty()) {
								System.out.println("AllowedFeatureCombination part 2: " + combination);
								cf = new SequentFormula(
										termBuilder.parseTerm("" + combination, goal.getLocalNamespaces()));
								goal.removeFormula(posInOccurrence);
								goal.addFormula(cf, false, false);
								seqSize = goal.sequent().size();
							}
						}
					}
				}
			}

		} catch (ParserException e) {
			System.out.println("Parsing the Sequent failed");
			e.printStackTrace();
		}
	}

	/**
	 * 
	 * @param className
	 * @param methodName
	 */
	private static void changeRecord(String className, String methodName) {
		Record record = recordMap.get(className).get(methodName);
		Method method = methodMap.get(className).get(methodName);
		if (record == null) {
			return;
		}

		if (method == null && methodName.contains("_")) {
			method = methodMap.get(className).get(methodName.split("_")[0]);
		}
		if (method == null) {
			System.out.println("Non Rigid 435 : could not find method " + methodName + "in methodmap");
			return;
		}

		if (!record.isPrepared()) {
			// check if there is a original method
			if (!method.getOriginal().isEmpty()) {
				// the original is added to the name
				record.setOriginalMethod(methodName.split("_")[0] + "_" + method.getOriginal());

				Method originalMethod = methodMap.get(className).get(record.getOriginalMethod().split("_")[0]);
				recordMap.get(className).put(methodName, prepareContracts(record, className, originalMethod));
				// change the record if the originalMethod
				changeRecord(className, record.getOriginalMethod());
			} else {
				// if there is no original method prepare the record
				recordMap.get(className).put(methodName, prepareContracts(record, className, method));
			}

			// if there are other methods are used in the method prepare the record
			List<String> usedFunctions = method.getCalledMethod();
			for (int i = 0; i < usedFunctions.size(); i++) {
				String methods = usedFunctions.get(i);
				if (!methods.isEmpty() && !methodName.equals(methods)) {
					if (methods.contains(".")) {
						String classString = methods.split("\\.")[0];
						classString = classString.substring(0, 1).toUpperCase() + classString.substring(1);
						String methodString = methods.split("\\.")[1];
						changeRecord(classString, methodString);
					} else {
						changeRecord(className, methods);
					}
				}
			}
		}
	}

	/**
	 * prepares the Recordentries of a method for inserting into sequents
	 * 
	 * @param contractsMap
	 * @param goal
	 */
	private static Record prepareContracts(Record record, String className, Method method) {

		if (record.getOriginalFrame() != "") {
			String frame = record.getOriginalFrame();
			if (frame.contains("\\nothing")) {
				frame = frame.replace("\\nothing", "");
			} else if (frame.contains("\\everything")) {
				frame = frame.replace("\\everything", "setMinus(allLocs, unusedLocs(heap))" + ", ");
			}
			boolean foundVariable = false;

			List<String> fields = method.getFields();
			for (String var : fields) {
				if (!var.isEmpty()) {
					if (frame.contains(var)) {
						if (var.contains(".")) {
							String[] twoStrings = var.split("\\.");
							String classString = twoStrings[0].substring(0, 1).toUpperCase()
									+ twoStrings[0].substring(1);
							frame = frame.replace(var,
									"elementOf(self," + classString + "::$" + twoStrings[1] + ",OriginalFrame)");
							foundVariable = true;
						} else {
							frame = frame.replace(var,
									"elementOf(self," + className + "::$" + var.trim() + ",OriginalFrame)");
							foundVariable = true;
						}
					}
				}
			}

			if (!frame.isEmpty() && !foundVariable) {
				String[] variables = frame.split(", ");
				List<String> variableList = new ArrayList<String>();
				for (String var : variables) {
					if (frame.contains(var)) {
						if (var.contains(".")) {
							String[] twoStrings = var.split("\\.");
							String classString = twoStrings[0].substring(0, 1).toUpperCase()
									+ twoStrings[0].substring(1);
							frame = frame.replace(var,
									"elementOf(self," + classString + "::$" + twoStrings[1] + ",OriginalFrame)");
							variableList.add(var);
						} else {
							frame = frame.replace(var,
									"elementOf(self," + className + "::$" + var.trim() + ",OriginalFrame)");
							variableList.add(var);
						}
					}
				}
				method.setFields(variableList);

			}
			record.setOriginalFrame(frame);
		}
		if (record.getOriginalPre() != "") {
			String pre = record.getOriginalPre();
			List<String> variables = method.getFields();
			for (String var : variables) {
				if (!var.isEmpty()) {
					if (pre.contains("\\old(" + var + ")")) {
						pre = pre.replace("\\old(" + var + ")", "self." + var + "@heapAtPre");
					} else if (pre.contains(var)) {
						if (var.contains(".")) {
							String tmpString = "(self ," + var + " & self.<inv>)& exc = null";
							pre = pre.replace(var, tmpString);
						} else {
							pre = pre.replace(var, "self." + var);
						}
					}
				}
			}

			for (String parameter : method.getParameter()) {
				if (!parameter.isEmpty()) {
					String p = parameter.split(" ")[1];
					if (methodMap.containsKey(parameter.split(" ")[0])) {
						pre = pre.replace(p, "self." + p);
					} else {
						pre = pre.replaceAll("(.*\\b)" + p + "(\\b.*)", "$1 _" + p + "$2");
					}
				}
			}
			pre = pre.replace(" || ", " | ");
			pre = pre.replace(" && ", " & ");
			pre = pre.replace(" == ", " = ");
			pre = pre.replace("(\\result)", "result = TRUE");
			pre = pre.replaceAll("(FM\\.FeatureModel\\.\\w+)", "$1=TRUE");
			record.setOriginalPre(pre);
		}
		if (record.getOriginalPost() != "") {
			String post = record.getOriginalPost();
			boolean foundVariable = false;
			List<String> variables = method.getFields();
			for (String var : variables) {
				if (!var.isEmpty()) {
					post = post.replace("\\old(" + var + ")", var + "@heapAtPre");
					post = post.replace(var, "self." + var);
					foundVariable = true;
				} /*
					 * if (foundVariable) { post = post + " & self.<inv>& exc = null"; }
					 */
			}
			for (String parameter : method.getParameter()) {
				if (!parameter.isEmpty()) {
					String p = parameter.split(" ")[1];
					post = post.replaceAll(" " + p + " ", " _" + p + " ");
				}
			}
			post = post.replace(" || ", " | ");
			post = post.replace(" && ", " & ");
			post = post.replace(" == ", " = ");
			post = post.replace("(\\result)", "result = TRUE");
			post = post.replaceAll("(FM\\.FeatureModel\\.\\w+)", "$1=TRUE");
			record.setOriginalPost(post);
		}
		if (!record.getCombination().isEmpty()) {
			String combination = record.getCombination();

			combination = combination.replaceAll("(FM\\.FeatureModel\\.\\w+)", "$1=TRUE");
			combination = combination.replace(" || ", " | ");
			combination = combination.replace(" && ", " & ");
			record.setCombination(combination);
		}
		record.setPrepared(true);
		return record;
	}

	private String getOtherOriginalPreString(Record record, String classString, String methodName) {
		String combinationPre = "";
		Record originalRecord = recordMap.get(classString).get(record.getOriginalMethod());
		Method method = methodMap.get(classString).get(methodName);
		if (method == null) {
			method = methodMap.get(classString).get(methodName.split("_")[0]);
		}
		if (originalRecord != null) {
			if (!originalRecord.isPrepared()) {
				changeRecord(classString, record.getOriginalMethod());
			}
			combinationPre = originalRecord.getOriginalPre();
		}

		List<String> calledMethods = method.getCalledMethod();
		if (!calledMethods.get(0).isEmpty()) {
			for (String methods : calledMethods) {
				if (methods.contains(".")) {
					String clazz = methods.split("\\.")[0];
					clazz = clazz.substring(0, 1).toUpperCase() + clazz.substring(1);
					String methodString = methods.split("\\.")[1];
					Record r = recordMap.get(clazz).get(methodString);
					if (r == null) {
						r = recordMap.get(clazz).get(methodString + "_" + method.getRootFeature());
					}
					if (combinationPre.isEmpty()) {
						combinationPre = r.getOriginalPre();
					} else if (!combinationPre.contains(r.getOriginalPre())) {
						combinationPre = combinationPre + " & " + r.getOriginalPre();
					}
				} else {
					Record r = recordMap.get(classString).get(methods);
					if (combinationPre.isEmpty()) {
						combinationPre = r.getOriginalPre();
					} else if (!combinationPre.contains(r.getOriginalPre())) {
						combinationPre = combinationPre + " & " + r.getOriginalPre();
					}
				}
			}
		}
		return combinationPre;
	}

	private String getOtherOriginalPostString(Record record, String classString, String methodName) {
		String combinationPost = "";
		Record originalRecord = recordMap.get(classString).get(record.getOriginalMethod());
		Method method = methodMap.get(classString).get(methodName);
		if (method == null) {
			method = methodMap.get(classString).get(methodName.split("_")[0]);
		}
		if (originalRecord != null) {
			if (!originalRecord.isPrepared()) {
				changeRecord(classString, record.getOriginalMethod());
			}
			combinationPost = originalRecord.getOriginalPost();
		}

		List<String> calledMethods = method.getCalledMethod();
		if (!calledMethods.get(0).isEmpty()) {
			for (String methods : calledMethods) {
				if (methods.contains(".")) {
					String clazz = methods.split("\\.")[0];
					clazz = clazz.substring(0, 1).toUpperCase() + clazz.substring(1);
					String methodString = methods.split("\\.")[1];
					Record r = recordMap.get(clazz).get(methodString);
					if (r == null) {
						r = recordMap.get(clazz).get(methodString + "_" + method.getRootFeature());
					}
					if (combinationPost.isEmpty()) {
						combinationPost = r.getOriginalPost();
					} else if (!combinationPost.contains(r.getOriginalPost())) {
						combinationPost = combinationPost + " & " + r.getOriginalPost();
					}
				} else {
					Record r = recordMap.get(classString).get(methods);
					if (combinationPost.isEmpty()) {
						combinationPost = r.getOriginalPost();
					} else if (!combinationPost.contains(r.getOriginalPost())) {
						combinationPost = combinationPost + " & " + r.getOriginalPost();
					}
				}
			}
		}
		return combinationPost;
	}

	private String getOtherOriginalFrameString(Record record, String classString, String methodName) {
		String combinationFrame = "";
		Record originalRecord = recordMap.get(classString).get(record.getOriginalMethod());
		Method method = methodMap.get(classString).get(methodName);
		if (method == null) {
			method = methodMap.get(classString).get(methodName.split("_")[0]);
		}
		if (originalRecord != null) {
			if (!originalRecord.isPrepared()) {
				changeRecord(classString, record.getOriginalMethod());
			}
			combinationFrame = originalRecord.getOriginalFrame();
		}

		List<String> calledMethods = method.getCalledMethod();
		if (!calledMethods.get(0).isEmpty()) {
			for (String methods : calledMethods) {
				if (methods.contains(".")) {
					String clazz = methods.split("\\.")[0];
					clazz = clazz.substring(0, 1).toUpperCase() + clazz.substring(1);
					String methodString = methods.split("\\.")[1];
					Record r = recordMap.get(clazz).get(methodString);
					if (r == null) {
						r = recordMap.get(clazz).get(methodString + "_" + method.getRootFeature());
					}
					if (combinationFrame.isEmpty()) {
						combinationFrame = r.getOriginalFrame();
					} else if (!combinationFrame.contains(r.getOriginalFrame())) {
						combinationFrame = combinationFrame + " & " + r.getOriginalFrame();
					}
				} else {
					Record r = recordMap.get(classString).get(methods);
					if (combinationFrame.isEmpty()) {
						combinationFrame = r.getOriginalFrame();
					} else if (!combinationFrame.contains(r.getOriginalFrame())) {
						combinationFrame = combinationFrame + " & " + r.getOriginalFrame();
					}
				}
			}
		}
		return combinationFrame;
	}

	private String getCombinationString(Record record, String classString, String methodName) {
		String combination = "";
		Record originalRecord = recordMap.get(classString).get(record.getOriginalMethod());
		Method method = methodMap.get(classString).get(methodName);
		if (method == null) {
			method = methodMap.get(classString).get(methodName.split("_")[0]);
		}
		if (originalRecord != null) {
			if (!originalRecord.isPrepared()) {
				changeRecord(classString, record.getOriginalMethod());
			}
			combination = originalRecord.getCombination();
		}

		List<String> calledMethods = method.getCalledMethod();
		if (!calledMethods.get(0).isEmpty()) {
			for (String methods : calledMethods) {
				if (methods.contains(".")) {
					String clazz = methods.split("\\.")[0];
					clazz = clazz.substring(0, 1).toUpperCase() + clazz.substring(1);
					String methodString = methods.split("\\.")[1];
					Record r = recordMap.get(clazz).get(methodString);
					if (r == null) {
						r = recordMap.get(clazz).get(methodString + "_" + method.getRootFeature());
					}
					if (combination.isEmpty()) {
						combination = r.getCombination();
					} else if (!combination.contains(r.getCombination())) {
						combination = combination + " & " + r.getCombination();
					}
				} else {
					Record r = recordMap.get(classString).get(methods);
					if (combination.isEmpty()) {
						combination = r.getCombination();
					} else if (!combination.contains(r.getCombination())) {
						combination = combination + " & " + r.getCombination();
					}
				}
			}
		}
		return combination;
	}

	/**
	 * 
	 * @param proof
	 * @param initConfig
	 * @param originalGoal
	 * @param reuseProof
	 * @param contractMap
	 * @param i
	 * @param recursionNr
	 * @param proofHandler
	 */
	private void proovingWithRecursion(Proof proof, String className, InitConfig initConfig, Goal originalGoal, int i,
			int recursionNr, ProofHandler proofHandler) {

		int goalNr = 1;
		for (Goal goal : proof.openGoals()) {
			System.out.println(goal.toString());
			String methodName = proofHandler.getTargetName().split("\\(")[0];
			Method method = methodMap.get(className).get(methodName);
			if (method == null) {
				method = methodMap.get(className).get(methodName.split("_")[0]);
			}
			if (method != null && !method.getOriginal().isEmpty()) {
				addInformationToGoal(methodName.split("_")[0] + "_" + method.getOriginal(), className,
						initConfig.getServices(), goal);
			}

			if (method != null) {
				List<String> usedFunctions = method.getCalledMethod();
				for (String function : usedFunctions) {
					if (!function.isEmpty()) {
						addInformationToGoal(function, className, initConfig.getServices(), goal);
					}
				}
			}
			addInformationToGoal(methodName, className, initConfig.getServices(), goal);

			InitConfig newconfig = initConfig.deepCopy();
			Proof newproof = new Proof(proof.name().toString(), goal.sequent(), proof.header(),
					newconfig.createTacletIndex(), newconfig.createBuiltInRuleIndex(), newconfig);
			int nrNodes = newproof.countNodes();
			/*
			 * keYEnvironment.getProofControl().runMacro(newproof.root(), new
			 * FullAutoPilotProofMacro(), null);
			 * keYEnvironment.getProofControl().waitWhileAutoMode();
			 */
			keYEnvironment.getProofControl().startAndWaitForAutoMode(proof);
			System.out.println("Goal Nr " + i + " of recursion " + recursionNr + " Goal " + goalNr + " of Proof: "
					+ newproof.name().toString() + " was Closed?: " + newproof.closed() + " \n"
					+ newproof.getStatistics());
			goalNr++;

			if (newproof.closed()) {
				proof.closeGoal(goal);
			} else if (nrNodes < proof.countNodes() || proof.countNodes() != 1) {

				proofHandler.addProofStatistic(proof);
				recursionNr++;
				proovingWithRecursion(newproof, className, initConfig, originalGoal, i, recursionNr, proofHandler);
			} else {
				return;
			}

		}
		if (proof.openGoals().isEmpty()) {
			System.out.println("Non_rigid Zeile 344 " + proof.name().toString() + " was Closed");
		}
	}

	/**
	 * Saves the proof in the given file
	 * 
	 * @param proofFile
	 */
	public File saveProof(String path, Proof proof) {
		final String defaultName = MiscTools.toValidFileName(proof.name().toString());
		File proofFile = new File(path + System.getProperty("file.separator") + defaultName + "1.proof");
		try {
			proof.saveToFile(proofFile);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return proofFile;
	}

	/**
	 * 
	 * @param proof
	 * @return
	 */
	public static boolean goalHasApplicableRules(Proof proof) {
		ImmutableList<Goal> goals = proof.openGoals();
		for (Goal g : goals) {
			if (SymbolicExecutionUtil.hasApplicableRules(g)) {
				return true;
			}
		}
		return false;
	}
}
