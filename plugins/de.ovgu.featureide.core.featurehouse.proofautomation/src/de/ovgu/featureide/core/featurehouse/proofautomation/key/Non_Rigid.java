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

			ProofControl proofControl = environment.getUi().getProofControl();
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
			String methodName = proofHandler.getTargetName();
			if (!methodName.equals("<inv>")) {
				methodName = methodName.split("\\(")[0];
			}

			System.out.println("Starte proof of  " + proofHandler.proof.name());
			proofHandler.setReusedStatistics();
			proofHandler.setStatistics();
			System.out.println("Reused: " + proofHandler.getTargetName() + "\n" + proofHandler.proof.getStatistics());
			int i = 1;

			for (Goal goal : proofHandler.proof.openGoals()) {

				SequentFormula cf;
				TermBuilder termBuilder = services.getTermBuilder();
				List<SequentFormula> seqents = goal.sequent().asList().toList();
				int allreadysetOriginalPre = 0;
				int allreadysetOriginalPost = 0;
				int allreadysetOriginalFrame = 0;
				int allreadysetCombination = 0;

				changeRecord(proofHandler.getTypeName(), methodName);
				Record record = recordMap.get(proofHandler.getTypeName()).get(methodName);

				try {
					if (record != null) {
						for (int j = 1; j < seqents.size(); j++) {
							PosInOccurrence posInOccurrence = PosInOccurrence.findInSequent(goal.sequent(), j,
									PosInTerm.getTopLevel());
							String sequent = seqents.get(j).toString();
							if (sequent.contains("OriginalPre<<origin") && record.getOriginalPre() != "") {
								if (allreadysetOriginalPre == 0) {
									PosInOccurrence pio = new PosInOccurrence(seqents.get(j + 1),
											PosInTerm.getTopLevel(), true);
									System.out.println("OriginalPre: " + record.getOriginalPre());
									cf = new SequentFormula(
											termBuilder.parseTerm("OriginalPre <->(" + record.getOriginalPre() + ")",
													goal.getLocalNamespaces()));
									goal.addFormula(cf, pio);
									allreadysetOriginalPre++;
								}

							}
							if (sequent.contains("OriginalPost<<origin") && record.getOriginalPost() != "") {
								if (allreadysetOriginalPost == 0) {
									System.out.println("OriginalPost: " + record.getOriginalPost());
									cf = new SequentFormula(
											termBuilder.parseTerm("OriginalPost <-> (" + record.getOriginalPost() + ")",
													goal.getLocalNamespaces()));
									goal.addFormula(cf, true, false);
									allreadysetOriginalPost++;
								}

							}
							if (sequent.contains("OriginalFrame<<origin") && !record.getOriginalFrame().isEmpty()) {
								if (allreadysetOriginalFrame == 0) {
									System.out.println("OriginalFrame: " + record.getOriginalFrame());
									cf = new SequentFormula(termBuilder.parseTerm(record.getOriginalFrame(),
											goal.getLocalNamespaces()));
									goal.addFormula(cf, true, false);
								}
							}
							if (sequent.contains("AllowedFeatureCombination") && !record.getCombination().isEmpty()) {
								if (allreadysetCombination == 0) {
									System.out.println("AllowedFeatureCombination: " + record.getCombination());
									if (posInOccurrence.isInAntec()) {
										cf = new SequentFormula(termBuilder.parseTerm("" + record.getCombination(),
												goal.getLocalNamespaces()));
										goal.addFormula(cf, true, false);
										allreadysetCombination++;
									}
									
								} else {									
										cf = new SequentFormula(termBuilder.parseTerm(""
												+ getCombinationString(record, proofHandler.getTypeName(), methodName),
												goal.getLocalNamespaces()));
										goal.addFormula(cf, false, false);									
								}
							}
						}
					}

				} catch (ParserException e) {
					System.out.println("Parsing the Sequent failed");
					e.printStackTrace();
				}
				// create new Proof with goal as root
				InitConfig config = proofHandler.proof.getInitConfig().deepCopy();

				Proof proof = new Proof(proofHandler.proof.name().toString(), goal.sequent(),
						proofHandler.proof.header(), config.createTacletIndex(), config.createBuiltInRuleIndex(),
						config);
				int nrNodes = proof.countNodes();
				ProofControl proofControl = keYEnvironment.getProofControl();
				FullAutoPilotProofMacro fappm = new FullAutoPilotProofMacro();
				// run the marco and than the proofing
				proofControl.runMacro(proof.root(), fappm, null);
				proofControl.waitWhileAutoMode();

				System.out.println("Goal " + i + " with new Proof " + proof.name().toString() + " was Closed?: "
						+ proof.closed() + " \n" + proof.getStatistics());
				proofHandler.addProofStatistic(proof);

				int recursionNr = 1;
				if (proof.closed()) {
					proofHandler.proof.closeGoal(goal);
				} else if (nrNodes < proof.countNodes() && !proof.closed()) {
					proovingWithRecursion(proof, proofHandler.getTypeName(), proofHandler.proof.getInitConfig(), goal,
							i, recursionNr, proofHandler);
					if (proof.closed()) {
						proofHandler.proof.closeGoal(goal);
					}
				} else {
					proovingWithRecursion(proof, proofHandler.getTypeName(), proofHandler.proof.getInitConfig(), goal,
							i, recursionNr, proofHandler);
					if (proof.closed()) {
						proofHandler.proof.closeGoal(goal);
					}
				}
				i++;
			}
			reusedAProof = true;
			if (!proofHandler.proof.openGoals().isEmpty()) {
				keYEnvironment.getProofControl().startAndWaitForAutoMode(proofHandler.proof);
				// overwrite the other statistic of the goal-proof because they did not close
				proofHandler.setStatistics();
				System.out.println(proofHandler.getTargetName() + "was Closed with startAndWaitForAutoMode ?: "
						+ proofHandler.proof.closed());
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

	private String getCombinationString(Record record, String classString, String methodName) {
		String combination = "";
		Record originalRecord = recordMap.get(classString).get(record.getOriginalMethod());
		Method method = methodMap.get(classString).get(methodName);
		if(method == null) {
			method = methodMap.get(classString).get(methodName.split("_")[0]);
		}
		if (originalRecord!= null) {			
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
					if(r == null) {
						r = recordMap.get(clazz).get(methodString+"_"+method.getRootFeature());
					}
					if (combination.isEmpty()) {
						combination = r.getCombination();
					} else if(!combination.contains(r.getCombination())){
						combination = combination + " & " + r.getCombination();
					}
				} else {
					Record r = recordMap.get(classString).get(methods);
					if (combination.isEmpty()) {
						combination = r.getCombination();
					} else if(!combination.contains(r.getCombination())) {
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
			String methodName = proofHandler.getTargetName().split("\\(")[0];
			Method method = methodMap.get(className).get(methodName);
			if(method == null) {
				method = methodMap.get(className).get(methodName.split("_")[0]);
			}
			if (method != null && !method.getOriginal().isEmpty()) {
				replaceOriginal(methodName.split("_")[0] + "_" + method.getOriginal(), className,
						initConfig.getServices(), goal, originalGoal);
			}

			if (method != null) {
				List<String> usedFunctions = method.getCalledMethod();
				for (String function : usedFunctions) {
					if (!function.isEmpty()) {
						replaceOriginal(function, className, initConfig.getServices(), goal, originalGoal);
					}
				}
			}
			replaceOriginal(methodName, className, initConfig.getServices(), goal, originalGoal);

			InitConfig newconfig = initConfig.deepCopy();
			Proof newproof = new Proof(proof.name().toString(), goal.sequent(), proof.header(),
					newconfig.createTacletIndex(), newconfig.createBuiltInRuleIndex(), newconfig);
			int nrNodes = newproof.countNodes();
			keYEnvironment.getProofControl().runMacro(newproof.root(), new FullAutoPilotProofMacro(), null);
			keYEnvironment.getProofControl().waitWhileAutoMode();

			System.out.println("Goal Nr " + i + " of recursion " + recursionNr + " Goal " + goalNr + " of Proof: "
					+ newproof.name().toString() + " was Closed?: " + newproof.closed() + " \n"
					+ newproof.getStatistics());
			goalNr++;

			if (newproof.closed()) {
				proofHandler.addProofStatistic(proof);
				proof.closeGoal(goal);
			} else if (nrNodes < proof.countNodes()) {
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
		if(method == null) {
			System.out.println("Non Rigid 435 : could not find method " + methodName + "in methodmap");
		}

		if (!record.isPrepared()) {
			// check if there is a original method
			if (!method.getOriginal().isEmpty()) {		
				//the original is added to the name
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
							String tmpString = "(self" + var + " & self.<inv>)& exc = null";
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
				}
				if (foundVariable) {
					post = post + " & self.<inv>& exc = null";
				}
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
	 * @param reuseProof
	 * @param services
	 * @param goal
	 * @param oldgoal
	 * @param oldContractMap
	 * @return
	 */
	private boolean replaceOriginal(String methodName, String className, Services services, Goal goal, Goal oldgoal) {

		boolean changedBoolean = false;
		boolean allreadysetOriginalPre = false;
		boolean allreadysetOriginalPost = false;
		boolean allreadysetOriginalFrame = false;
		boolean allreadysetCombination = false;

		SequentFormula cf;
		TermBuilder termBuilder = services.getTermBuilder();
		Sequent seqent = goal.sequent();
		Record record = recordMap.get(className).get(methodName);
		if (record == null) {
			return false;
		}
		if (!record.isPrepared()) {
			changeRecord(className, methodName);
			record = recordMap.get(className).get(methodName);
		}
		int precount = 0;
		int postcount = 0;
		int allowedcount = 0;
		try {
			for (int i = 1; i < seqent.size(); i++) {
				PosInOccurrence posInOccurrence = PosInOccurrence.findInSequent(goal.sequent(), i,
						PosInTerm.getTopLevel());
				String sqString = seqent.getFormulabyNr(i).toString();
				if (sqString.contains("equiv(OriginalPre")) {
					precount++;
				}
				if (!allreadysetOriginalPre && precount > 0 && sqString.contains("OriginalPre<<origin")
						&& record.getOriginalPre() != "") {
					cf = new SequentFormula(termBuilder.parseTerm("OriginalPre <-> " + record.getOriginalPre(),
							oldgoal.getLocalNamespaces()));

					PosInOccurrence piOccurrence = new PosInOccurrence(seqent.getFormulabyNr(i),
							PosInTerm.getTopLevel(), true);
					goal.removeFormula(piOccurrence);
					goal.addFormula(cf, true, false);
					allreadysetOriginalPre = true;

				}
				if (sqString.contains("equiv(OriginalPost")) {
					postcount++;
				}
				if (!allreadysetOriginalPost && postcount > 0 && sqString.contains("OriginalPost<<origin")
						&& record.getOriginalPost() != "") {
					cf = new SequentFormula(termBuilder.parseTerm("OriginalPost <-> " + record.getOriginalPost(),
							oldgoal.getLocalNamespaces()));
					goal.addFormula(cf, true, false);
					allreadysetOriginalPost = true;

				}
				if (!allreadysetOriginalFrame && sqString.contains("OriginalFrame")
						&& record.getOriginalFrame() != "") {
					cf = new SequentFormula(
							termBuilder.parseTerm(record.getOriginalFrame(), oldgoal.getLocalNamespaces()));
					goal.addFormula(cf, true, false);
					allreadysetOriginalFrame = true;
				}
				// beim zweiten suchen
				if (sqString.contains("AllowedFeatureCombination<<origin")) {
					allowedcount++;
				}
				if (!allreadysetCombination && allowedcount > 1
						&& sqString.contains("AllowedFeatureCombination<<origin")) {
					cf = new SequentFormula(termBuilder.parseTerm(
							"AllowedFeatureCombination<->" + record.getCombination(), goal.getLocalNamespaces()));

					if (!posInOccurrence.isInAntec()) {
						String combinationString = getCombinationString(record, className, methodName);
						if (!combinationString.isEmpty()) {
							System.out.println("AllowedFeatureCombination: " + combinationString);
							cf = new SequentFormula(
									termBuilder.parseTerm("AllowedFeatureCombination<->" + combinationString, goal.getLocalNamespaces()));
							goal.addFormula(cf, false, false);
						}
						allowedcount++;
						allreadysetCombination = true;
					}

				}
			}

			if (!(allreadysetOriginalPre || allreadysetOriginalPost || allreadysetOriginalFrame
					|| allreadysetCombination)) {
				changedBoolean = false;
			} else {
				changedBoolean = true;
			}
		} catch (ParserException e) {
			System.out.println("Non_Rigid startMetaProductProof failed");
			e.printStackTrace();
		}
		return changedBoolean;
	}

	/**
	 * 
	 * @param goal
	 * @return
	 */
	private static List<String> getUsedFunktions(Goal goal) { // new version
		List<String> usedFunctions = new ArrayList<>();
		for (Function function : goal.node().getLocalFunctions()) {
			function.name();
			String name = function.name().toString();
			if (name.contains("anon_heap_")) {
				String subString = name.substring("anon_heap_".length());
				usedFunctions.add(subString);
				// System.out.println(subString);
			}
		}
		return usedFunctions;
	}
}
