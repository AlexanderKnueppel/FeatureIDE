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

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.key_project.util.collection.ImmutableList;

import de.ovgu.featureide.core.featurehouse.proofautomation.builder.BuilderUtil;
import de.ovgu.featureide.core.featurehouse.proofautomation.filemanagement.FileManager;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.IntIterator;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.parser.ParserException;
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
			int maxRuleApplication, String savePath) {
		UserInterfaceControl userInterface = new DefaultUserInterfaceControl(null);
		boolean reusedAProof = false;
		System.out.println("\n Reuse proof: " + reuseProof.getName());

		try {
			AbstractProblemLoader loader = userInterface.load(null, reuseProof, null, null, null, sp, false);
			InitConfig initConfig = loader.getInitConfig();
			KeYEnvironment<?> keYEnvironment = new KeYEnvironment<>(userInterface, initConfig, loader.getProof(),
					loader.getProofScript(), loader.getResult());
			Services services = keYEnvironment.getServices();

			proofHandler.proof = keYEnvironment.getLoadedProof();
			
			proofHandler.setReusedStatistics();
			System.out.println(
					"Reused: " + proofHandler.getTargetName() + "\n" + proofHandler.proof.getStatistics());			
			int i = 0;
			for (Goal goal : proofHandler.proof.openGoals()) {
				
				SequentFormula cf;

				TermBuilder termBuilder = services.getTermBuilder();
				Map<String, String> contractMap = getContract(reuseProof, goal);
				Sequent seqent = goal.sequent();
				boolean allreadysetOriginalPre = false;
				boolean allreadysetOriginalPost = false;
				boolean allreadysetOriginalFrame = false;
				boolean allreadysetCombination = false;
				try {
					if (contractMap != null) {
						for (SequentFormula sequentFormula : seqent) {
							//PosInOccurrence posInOccurrence = new PosInOccurrence(sequentFormula,
							//		PosInTerm.getTopLevel(), true);
							if (!allreadysetOriginalPre && sequentFormula.toString().contains("OriginalPre")
									&& contractMap.containsKey("originalPre")) {
								cf = new SequentFormula(
										termBuilder.parseTerm("OriginalPre <-> " + contractMap.get("originalPre"),
												goal.getLocalNamespaces()));
								goal.addFormula(cf, true, false);
								allreadysetOriginalPre = true;
							}
							if (!allreadysetOriginalPost && sequentFormula.toString().contains("OriginalPost")
									&& contractMap.containsKey("originalPost")) {
								System.out.println("OriginalPost: " +contractMap.get("originalPost"));
								cf = new SequentFormula(
										termBuilder.parseTerm("OriginalPost <-> " + contractMap.get("originalPost"),
												goal.getLocalNamespaces()));
								goal.addFormula(cf, true, false);
								allreadysetOriginalPost = true;
							}
							if (!allreadysetOriginalFrame && sequentFormula.toString().contains("OriginalFrame")
									&& contractMap.containsKey("originalFrame")) {
								System.out.println("OriginalFrame: " +contractMap.get("originalFrame"));
								cf = new SequentFormula(
										termBuilder.parseTerm(contractMap.get("originalFrame"),
												goal.getLocalNamespaces()));
								goal.addFormula(cf, true, false);
								allreadysetOriginalFrame = true;
							}
							if (!allreadysetCombination
									&& sequentFormula.toString().contains("AllowedFeatureCombination")
									&& contractMap.containsKey("combination")) {
								System.out.println("AllowedFeatureCombination: " +contractMap.get("combination"));
								cf = new SequentFormula(termBuilder.parseTerm(
										"AllowedFeatureCombination <-> " + contractMap.get("combination"),
										goal.getLocalNamespaces()));
								goal.addFormula(cf, true, false);
								allreadysetCombination = true;
							}
						}
					}
				} catch (ParserException e) {
					System.out.println("Parsing the Sequent failed");
					e.printStackTrace();
				}
				/*
				Node goalNode = goal.node();
				Services services2 = new Services(keYEnvironment.getProfile());
				InitConfig initConfig2 = new InitConfig(services2);
				Proof proof = new Proof(proofHandler.proof.name().toString()+i, initConfig2);
				
				proof.setRoot(goalNode);
				ProofEnvironment environment = new ProofEnvironment(initConfig2);
				
				proof.setEnv(environment);
				proof.setActiveStrategy(proofHandler.proof.getActiveStrategy());
				proof.add(goal);
				proof.setNamespaces(services2.getNamespaces());
				
				keYEnvironment.getProofControl().startAndWaitForAutoMode(proof);
				System.out.println(proof.name().toString() +" was Closed?: " + proof.closed()+ " \n" + proof.getStatistics());
				proof.dispose();*/
				//System.out.println(proof.toString());
				//File reusedProof = saveProof(savePath, proof);
				//replaceJavaSource(reusedProof);
				i++;
				
			}
			
			
			keYEnvironment.getProofControl().startAndWaitForAutoMode(proofHandler.proof);

			reusedAProof = true;
			System.out.println( proofHandler.getTargetName() +"was Closed?: " + proofHandler.proof.closed());
			/*File reusedProof = null;
			if (!proofHandler.proof.closed()) {
				reusedProof = proofHandler.saveProof(savePath);
				replaceJavaSource(reusedProof);
				
				 * loader = userInterface.load(null, reuseProof, null, null, null, null, false);
				 * initConfig = loader.getInitConfig(); keYEnvironment = new
				 * KeYEnvironment<>(userInterface, initConfig, loader.getProof(),
				 * loader.getProofScript(), loader.getResult());
				 
				keYEnvironment = KeYEnvironment.load(reusedProof);				
				proofHandler.proof = keYEnvironment.getLoadedProof();
				reusedProof.delete();
				int previousNodes;
				int numberofOpenGoal = proofHandler.proof.openGoals().size();
				do {
					if (proofHandler.proof.closed()) {
						break;
					}
					numberofOpenGoal = proofHandler.proof.openGoals().size();
					
					for (Goal goal : proofHandler.proof.openGoals()) {
						replaceOriginal(goal, reuseProof, services);
					}
					previousNodes = proofHandler.proof.countNodes();
					keYEnvironment.getProofControl().startAndWaitForAutoMode(proofHandler.proof);
					proofHandler.setProof(proofHandler.proof);
					System.out.println(
							"Open goals of " + proofHandler.getTargetName() + " in " + proofHandler.getTypeName()
									+ " has " + proofHandler.proof.openGoals().size() + " open Goals");
					System.out.println(previousNodes + " " + proofHandler.proof.countNodes());

				} while (numberofOpenGoal != proofHandler.proof.openGoals().size()
						);

			}
*/
			if (proofHandler.proof.openGoals().isEmpty()) {
				System.out.println("Metaproductproof of " + proofHandler.getTargetName() + " in "
						+ proofHandler.getTypeName() + " was closed");
				proofHandler.setClosed(true);
			}
		} catch (ProblemLoaderException e) {
			System.out.println("Exception at '" + proofHandler.getTargetName() + ":");
			throw new RuntimeException(e);
		}
		proofHandler.setProof(proofHandler.proof);
		proofHandler.setStatistics();
		System.out.println("Actual: " + proofHandler.getTargetName() + "\n" + proofHandler.proof.getStatistics());

		return reusedAProof;
	}

//	private static Map<String, String> getOriginalInformation(File reuseProof, Goal goal) { //new version
//		proofHandler.proof.
//	}
	
	
private void replaceOriginal(Goal newGoal, File reuseProof, Services services) {
	SequentFormula cf;

	TermBuilder termBuilder = services.getTermBuilder();

	Map<String, String> contractMap = getContract(reuseProof, newGoal);
	Sequent seqent = newGoal.sequent();
	boolean allreadysetOriginalPre = false;
	boolean allreadysetOriginalPost = false;
	boolean allreadysetOriginalFrame = false;
	boolean allreadysetCombination = false;
	try {
		if (contractMap != null) {
			for (SequentFormula sequentFormula : seqent) {
				PosInOccurrence posInOccurrence = new PosInOccurrence(sequentFormula,
						PosInTerm.getTopLevel(), true);
				if (!allreadysetOriginalPre && sequentFormula.toString().contains("OriginalPre")
						&& contractMap.containsKey("originalPre")) {
					cf = new SequentFormula(
							termBuilder.parseTerm("OriginalPre <-> " + contractMap.get("originalPre"),
									newGoal.getLocalNamespaces()));
					newGoal.addFormula(cf, true, false);
					allreadysetOriginalPre = true;
				}
				if (!allreadysetOriginalPost && sequentFormula.toString().contains("OriginalPost")
						&& contractMap.containsKey("originalPost")) {
					cf = new SequentFormula(
							termBuilder.parseTerm("OriginalPost <-> " + contractMap.get("originalPost"),
									newGoal.getLocalNamespaces()));
					newGoal.addFormula(cf, true, false);
					allreadysetOriginalPost = true;
				}
				if (!allreadysetOriginalFrame && sequentFormula.toString().contains("OriginalFrame")
						&& contractMap.containsKey("originalFrame")) {
					cf = new SequentFormula(
							termBuilder.parseTerm(contractMap.get("originalFrame"),
									newGoal.getLocalNamespaces()));
					newGoal.addFormula(cf, true, false);
					allreadysetOriginalFrame = true;
				}
				if (!allreadysetCombination
						&& sequentFormula.toString().contains("AllowedFeatureCombination")
						&& contractMap.containsKey("combination")) {
					cf = new SequentFormula(termBuilder.parseTerm(
							"AllowedFeatureCombination <-> " + contractMap.get("combination"),
							newGoal.getLocalNamespaces()));
					newGoal.addFormula(cf, true, false);
					allreadysetCombination = true;
				}
			}
		}
	}catch (ParserException e) {
		System.out.println("Non_Rigid startMetaProductProof failed");
		e.printStackTrace();
	}		
		
}
	/**
	 * Searches in the Metaproduct for the right contracts
	 * 
	 * @param reuseProof
	 * @return
	 */
	private static Map<String, String> getContract(File reuseProof, Goal goal) {
		String folderString = reuseProof.getParentFile().getParentFile().getParentFile().getName();
		String proofPath = reuseProof.getParentFile().getParentFile().getParentFile().getParentFile().getParentFile()
				.getParentFile().getParentFile().getAbsolutePath() + FILE_SEPERATOR + folderString + FILE_SEPERATOR
				+ FileManager.metaproductDir;
		String[] tmpString = reuseProof.getName().split("_");
		String methodName = "";
		if (tmpString.length <= 2) {
			methodName = tmpString[1].replace(".proof", "");
		} else {
			methodName = tmpString[1] + "_" + tmpString[2];
			methodName = methodName.replace(".proof", "");
		}
		String className = tmpString[0];

		try {
			if (new File(proofPath + FILE_SEPERATOR + className + ".java").exists()) {

				BufferedReader bReader = new BufferedReader(
						new FileReader(proofPath + FILE_SEPERATOR + className + ".java"));
				String line = bReader.readLine();
				Map<String, String> contractsMap = new HashMap<>();
				contractsMap.clear();
				while (line != null) {
					for (int i = 0; i < jml.length; i++) {
						if (line.contains("_" + jml[i] + "_" + methodName)) {
							String[] contract = line.split(" = ", 2);
							if (contract.length > 1) {
								contractsMap.put(jml[i], contract[1]);
							}
						}
					}
					line = bReader.readLine();
				}
				bReader.close();
				prepareContracts(contractsMap, goal,className);
				return contractsMap;
			} else {
				System.out.println("Non_Rigid Line 312: File " + className + ".java" + " does not exist");
			}

		} catch (IOException e) {
			System.out.println("Non_Rigid getContract");
			e.printStackTrace();
		}
		return null;
	}

	/**
	 * 
	 * @param contractsMap
	 * @param goal
	 */
	private static void prepareContracts(Map<String, String> contractsMap, Goal goal,String className) {
		List<String> variableList = new LinkedList<>();
		for (int i = 0; i <= 3; i++) {
			if (contractsMap.containsKey(jml[i])) {
				String value = contractsMap.get(jml[i]);
				if (jml[i].equals("originalFrame")) {
					String[] variables = value.split(",");
					value = "";
					for (String var : variables) {
						var = var.trim();

						if (var.contains("\\nothing")) {
							var = var.replace("\\nothing", "");
							value = "";
						}
						if(var.contains("\\everything")) {
							var = var.replace("\\everything", "");
							value =  "setMinus(allLocs, unusedLocs(heap))" + ", ";
						}
						if (!var.isEmpty()) {
							variableList.add(var);
							if(var.contains(".")) {
								System.out.println(var);
								String[] twoStrings = var.split("\\.");
								String classString = twoStrings[0].substring(0, 1).toUpperCase() + twoStrings[0].substring(1);
								var = "elementOf(self,"+classString+"::$" + twoStrings[1]+",OriginalFrame)";
							}else {
								var = "elementOf(self,"+className+"::$" + var.trim()+",OriginalFrame)";
							}
							
							value = value + var + ", ";
						}
					}

					if (value.length() != 0) {
						if (!value.equals("empty")) {
							value = value.substring(0, value.length() - 2);
						}
					} else {
						value = null;
					}
				}		
				else {
					if (value.trim() != null) {
						for (String var : variableList) {
							if (value.contains("\\old(" + var + ")")) {
								value = value.replace("\\old(" + var + ")", "self." + var + "@heapAtPre");
							}else if(value.contains(var)){
								
							//	String[] twoStrings = var.split(".");
								value = value.replace(var,"self."+var);
							}
						}
						
						value = value.replace("x ", "_x ");
						value = value.replace("OVERDRAFT_LIMIT", "self.OVERDRAFT_LIMIT");
						value = value.replace(" || ", " | ");
						value = value.replace(" && ", " & ");
						value = value.replace(" == ", " = ");
						value = value.replace("(\\result)", "result = TRUE");
						value = "(" + value + ")";
						value = value.replaceAll("(FM\\.FeatureModel\\.\\w+)", "$1=TRUE");
					}										
								}
				if (value != null) {
					contractsMap.put(jml[i], value);
				} else {
					contractsMap.remove(jml[i]);
				}
			}
		}
	}

	private JavaModel getFittingNamespace(File reuseProof) {
		String folderString = reuseProof.getParentFile().getParentFile().getParentFile().getName();
		String metaPath = reuseProof.getParentFile().getParentFile().getParentFile().getParentFile().getParentFile()
				.getParentFile().getParentFile().getAbsolutePath() + FILE_SEPERATOR + folderString + FILE_SEPERATOR
				+ FileManager.metaproductDir;
		String[] tmpString = reuseProof.getName().split("\\(");
		String methodName = "";
		if (tmpString.length < 2) {
			tmpString = reuseProof.getName().split("_");
			methodName = tmpString[1];
		} else {
			methodName = tmpString[1].substring(tmpString[1].lastIndexOf("__") + 2);
		}
		String featureName = tmpString[0];
		if (new File(metaPath + FILE_SEPERATOR + featureName + ".java").exists()) {

			// System.out.print(initConfig.getServices().getNamespaces());
			List<ProofHandler> proofList = loadInKeY(new File(metaPath + FILE_SEPERATOR + featureName + ".java"));
			for (ProofHandler proofHandler : proofList) {
				KeYEnvironment<?> environment = proofHandler.getEnvironment();
				Contract contract = proofHandler.getContract();
				String name = contract.getTarget().toString();
				if (name.contains(methodName + "_BankAccount")) {
					return environment.getInitConfig().getServices().getJavaModel();
				}

			}
		}
		return null;
	}
	
	/**
	 * Saves the proof in the given file
	 * @param proofFile
	 */
	public File saveProof(String path, Proof proof){
		final String defaultName = MiscTools.toValidFileName(proof.name().toString());
		File proofFile = new File(path+System.getProperty("file.separator")+defaultName+".proof");
		
			StringBuffer sbuffer = new StringBuffer();
			sbuffer.append(proof.toString());
			BuilderUtil.rewriteFile(sbuffer,proofFile);
			//proof.saveToFile(proofFile);
				return proofFile;
	}
}
