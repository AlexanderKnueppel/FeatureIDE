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

import de.ovgu.featureide.core.featurehouse.proofautomation.filemanagement.FileManager;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.java.Services;
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

import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.strategy.Strategy;

import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.MiscTools;

/**
 * TODO description
 * @author Marlen Herter-Bernier
 */
public class Non_Rigid extends KeyHandler{
	public static String FILE_SEPERATOR = System.getProperty("file.separator");
	private static String[] jml = {"assignable","requires","ensures"};	

	
	/** Initializes the abstract execution proof  
	 * @param oldPartialProof
	 * @param maxRuleApplication
	 * @param defaultSettingsForFeatureStub
	 */
	public void startAbstractProof(ProofHandler proofHandler, int maxRuleApplication, StrategyProperties sp) {
		KeYEnvironment<?> environment = proofHandler.getEnvironment();
		Contract contract = proofHandler.getContract();
		
		try{
			
		    ProofOblInput input = contract.createProofObl(environment.getInitConfig(), contract);
		    proofHandler.proof = environment.createProof(input);

			// Set proof strategy options
	        ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
	        HashMap<String,String> choices = proofHandler.proof.getSettings().getChoiceSettings().getDefaultChoices();
	        choices.putAll(MiscTools.getDefaultTacletOptions());
	        choiceSettings.setDefaultChoices(choices);
	        
	        proofHandler.proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
        	ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(maxRuleApplication);
        	ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(sp);
        	proofHandler.proof.getSettings().getStrategySettings().setMaxSteps(maxRuleApplication);
        	proofHandler.proof.setActiveStrategy(proofHandler.proof.getServices().getProfile().getDefaultStrategyFactory().create(proofHandler.proof, sp));
			
	        ProofControl proofControl = environment.getUi().getProofControl();
			int previousNodes;
			do{
				previousNodes = proofHandler.proof.countNodes();
	
				proofControl.startAndWaitForAutoMode(proofHandler.proof);
	
			}while(proofHandler.proof.countNodes()==previousNodes);
	        if(proofHandler.proof.openGoals().isEmpty()){
	        	System.out.println("Proof " +proofHandler.proof.name() + " was closed");
	        	proofHandler.setClosed(true);
	        }
	        proofHandler.setStatistics();
	        environment.dispose();
		} catch (ProofInputException e) {
            System.out.println("Exception at '" + contract.getDisplayName() + "' of " + contract.getTarget() + ":");
            e.printStackTrace();
		}	
	}
	
	public boolean startMetaProductProof(ProofHandler proofHandler,File reuseProof,  StrategyProperties sp, int maxRuleApplication, String savePath) {
		UserInterfaceControl userInterface = new DefaultUserInterfaceControl(null);
		boolean reusedAProof = false;
		
		System.out.println("\n Reuse proof: " + reuseProof.getName());
		
		try {
			AbstractProblemLoader loader = userInterface.load(null, reuseProof, null, null, null, null, false);
			InitConfig initConfig = loader.getInitConfig();
			KeYEnvironment<?> keYEnvironment = new KeYEnvironment<>(userInterface, initConfig, loader.getProof(), loader.getProofScript(),loader.getResult());		
			Services services = keYEnvironment.getServices();			
			
			proofHandler.proof = keYEnvironment.getLoadedProof();
			
			for(Goal goal : proofHandler.proof.openGoals()) {
				Goal oldGoal = goal;
				SequentFormula cf;

				TermBuilder termBuilder = services.getTermBuilder();				
				Map<String,String> contractMap = getContract(reuseProof,goal);
				Sequent seqent = goal.sequent();
				
				boolean allreadyset = false;
				try {
					if(contractMap != null) {
									
						for(SequentFormula sequentFormula:seqent) {
							PosInOccurrence posInOccurrence = new PosInOccurrence(sequentFormula,PosInTerm.getTopLevel(), true);
							if(! allreadyset && (sequentFormula.toString().contains("OriginalPre")||sequentFormula.toString().contains("OriginalPost"))) {	
								if(contractMap.containsKey("requires")) {
									cf = new SequentFormula(termBuilder.parseTerm("OriginalPre <-> "+contractMap.get("requires"), goal.getLocalNamespaces()));
									goal.addFormula(cf, posInOccurrence);
									allreadyset=true;
								}
								if(contractMap.containsKey("ensures")) {
									cf = new SequentFormula(termBuilder.parseTerm("OriginalPost <-> "+contractMap.get("ensures"), goal.getLocalNamespaces()));	
									goal.addFormula(cf, posInOccurrence);
								}
								if(contractMap.containsKey("assignable")) {
									cf = new SequentFormula(termBuilder.parseTerm("OriginalFrame = "+contractMap.get("assignable"), goal.getLocalNamespaces()));							
									goal.addFormula(cf, posInOccurrence);
								}
							}								
						}
						if(allreadyset) {
							//System.out.println("before:\n"+oldGoal);
							//System.out.println("after:\n"+goal);
						}
					}
			
				} catch (ParserException e) {
					System.out.println("Non_Rigid startMetaProductProof failed");
					e.printStackTrace();
				}/*
				Node node = goal.node();
				Profile profile = keYEnvironment.getProfile();

				Services newServices = new Services(profile);
				InitConfig newinitConfig = new InitConfig(newServices);
				
				Proof prooNewProof = new Proof(node.name(), newinitConfig);
				prooNewProof.add(goal);
				prooNewProof.setRoot(node);				
				Strategy strategy = goal.getGoalStrategy();
				prooNewProof.setActiveStrategy(strategy);*/
				//prooNewProof.saveToFile(new File(reuseProof.getParentFile().getParentFile().getAbsolutePath() + FILE_SEPERATOR + proofHandler.proof.name()+ "_"+ k));	
				List<Goal>goals = new LinkedList<>();
				goals.add(goal);
				ImmutableList<Goal> goalsImmutableList = ImmutableList.fromList(goals);
				proofHandler.proof.replace(oldGoal, goalsImmutableList);
	
			}
			keYEnvironment.getProofControl().startAndWaitForAutoMode(proofHandler.proof);
        	proofHandler.setProof(proofHandler.proof);
			proofHandler.setReusedStatistics();	
        	reusedAProof = true;
        	System.out.println("Closed: " + proofHandler.proof.closed());
            System.out.println("Reused: "+ proofHandler.getTargetName()+"\n"+ proofHandler.getProof().getStatistics());
            proofHandler.setReusedStatistics();
            File reusedProof = null;
            if(!proofHandler.proof.closed()) {
            	reusedProof = proofHandler.saveProof(savePath);
	            replaceJavaSource(reusedProof);
	            /*
				loader = userInterface.load(null, reuseProof, null, null, null, null, false);
				initConfig = loader.getInitConfig();	
				keYEnvironment = new KeYEnvironment<>(userInterface, initConfig, loader.getProof(), loader.getProofScript(), loader.getResult());
	        	*/
	            keYEnvironment = KeYEnvironment.load(reusedProof);
				reusedProof.delete();
	        	proofHandler.proof = keYEnvironment.getLoadedProof();
		        int previousNodes;
		        int numberofOpenGoal = proofHandler.proof.openGoals().size();	        
		        do{
		        	if(proofHandler.proof.closed()) {
		        		break;
		        	}
		        	numberofOpenGoal = proofHandler.proof.openGoals().size();
					previousNodes = proofHandler.proof.countNodes();	
					keYEnvironment.getProofControl().startAndWaitForAutoMode(proofHandler.proof);
	            	proofHandler.setProof(proofHandler.proof);
		        	System.out.println("Open goals of " + proofHandler.getTargetName()+" in " +proofHandler.getTypeName()+" has " + proofHandler.proof.openGoals().size() +" open Goals" );
		        	System.out.println(previousNodes + " " + proofHandler.proof.countNodes()); 

					}while((numberofOpenGoal != proofHandler.proof.openGoals().size()) || (previousNodes != proofHandler.proof.countNodes()));
		        
            }

	        if(proofHandler.proof.openGoals().isEmpty()){
	        	System.out.println("Metaproductproof of " + proofHandler.getTargetName()+" in " +proofHandler.getTypeName()+" was closed");
	            proofHandler.setClosed(true);
	        }		
		} catch (ProblemLoaderException e) {
            System.out.println("Exception at '" + proofHandler.getTargetName() + ":");
			throw new RuntimeException(e);
		}
		proofHandler.setProof(proofHandler.proof);
		proofHandler.setStatistics();
        System.out.println("Actual: "+ proofHandler.getTargetName() +"\n" + proofHandler.proof.getStatistics());

		return reusedAProof;
	}
	
//	private static Map<String, String> getOriginalInformation(File reuseProof, Goal goal) { //new version
//		proofHandler.proof.
//	}
	
	
	/**
	 * Searches in the Metaproduct for the right contracts
	 * @param reuseProof
	 * @return
	 */
	private static Map<String, String> getContract(File reuseProof, Goal goal) {
        String folderString = reuseProof.getParentFile().getParentFile().getParentFile().getName();
        String projectName = folderString.substring(0,folderString.length()-2);
		String proofPath = reuseProof.getParentFile().getParentFile().getParentFile().getParentFile().getParentFile().getParentFile().getParentFile().getAbsolutePath()+FILE_SEPERATOR+folderString +FILE_SEPERATOR+FileManager.metaproductDir;
		String[] tmpString = reuseProof.getName().split("\\(");
		String methodName = "";
		if(tmpString.length < 2) {
			tmpString = reuseProof.getName().split("_");
			methodName = tmpString[1];
		}else {
			methodName = tmpString[1].substring(tmpString[1].lastIndexOf("__")+2);
		}
		String featureName = tmpString[0];
			
		try {
			if(new File(proofPath+FILE_SEPERATOR+featureName+".java").exists()) {
		
				BufferedReader bReader = new BufferedReader(new FileReader(proofPath+FILE_SEPERATOR+featureName+".java"));
	            String line = bReader.readLine();
	            Map<String, String> contractsMap = new HashMap<>();
	            while(line != null) {
	            	if(line.contains("/*@")){
	            		contractsMap.clear();
	            		line = line.replace("/*@","");
	            		while(!line.contains("@*/")&& !line.contains("/*@pure@*/")) {	            			             			 
	            			 String tmp = line.replace("@", "").trim();
	            			 for(int i = 0; i<=2;i++) {
	            				 if(tmp.contains(jml[i])) {	            					 
	            					 tmp = tmp.replace(jml[i], "");
		            				 String entry = contractsMap.get(jml[i]);
		            				 if(entry != null) {
		            					 entry = "(" + entry +") && ("+tmp.replaceAll(";", "")+")";
		            				 }else {
		            					 entry = tmp.replaceAll(";", "");
		            				 }
		            				 contractsMap.put(jml[i], entry);	
	            				 }
	            			 }
	            			 line = bReader.readLine().trim();
	            		}	            		
	            		line = bReader.readLine().trim();

		            	if(line.contains(methodName+"_" + projectName +"(") && line.endsWith("{")) {
		                 	prepareContracts(contractsMap,goal);
		                 	return contractsMap;
		            	}
	            	}          	
          	           	
	                line = bReader.readLine();
	            }
	            bReader.close();
			}else {
				System.out.println("Non_Rigid Line 199: File " +featureName+".java"+ " does not exist");
			}
			
        } catch(IOException e) {
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
	private static void prepareContracts(Map<String, String> contractsMap, Goal goal) {
		List<String> variableList = new LinkedList<>();
		for(int i = 0; i<=2;i++) {			
			if(contractsMap.containsKey(jml[i])) {
				String value = contractsMap.get(jml[i]);
				if(jml[i].equals("assignable")) {					
					String[] variables = value.split(",");					
					value = "";
					for(String var : variables) {
						var = var.trim();	
						
						if(var.contains("\\nothing")) {
							var = var.replace("\\nothing","");
							value = "null";
						}
						if(!var.isEmpty()) {
							variableList.add(var);
							var = "self." + var.trim();
							//value = String.join(", ", value,var);
							value = value +var + ", ";
						}
					}
					
					if(value.length() != 0) {
						if(!value.equals("null")) {
							value  = value.substring(0,value.length()-2);
						}
					}else {
						value = null;
					}
				}else{
					if(value.trim() != null) {
						for(String var: variableList) {
							if(value.contains("\\old("+var+")")) {
								value = value.replace("\\old("+var+")", "self."+var+"@heapAtPre");
							}
						}						
						value = value.replace("x ", "_x ");
						value = value.replace("OVERDRAFT_LIMIT", "self.OVERDRAFT_LIMIT");
						value = value.replace(" || ", " | ");
						value = value.replace(" && ", " & ");
						value = value.replace("(\\result)", "result = TRUE");	
						value = "("+value+")";
					}					
				}
				if(value != null) {
					contractsMap.put(jml[i], value);
				}else {
					contractsMap.remove(jml[i]);
				}
			}
		}
	}
	
	private JavaModel getFittingNamespace(File reuseProof) {
		String folderString = reuseProof.getParentFile().getParentFile().getParentFile().getName();
		String metaPath = reuseProof.getParentFile().getParentFile().getParentFile().getParentFile().getParentFile().getParentFile().getParentFile().getAbsolutePath()+FILE_SEPERATOR+folderString +FILE_SEPERATOR+FileManager.metaproductDir;
		String[] tmpString = reuseProof.getName().split("\\(");
		String methodName = "";
		if(tmpString.length < 2) {
			tmpString = reuseProof.getName().split("_");
			methodName = tmpString[1];
		}else {
			methodName = tmpString[1].substring(tmpString[1].lastIndexOf("__")+2);
		}
		String featureName = tmpString[0];
		if(new File(metaPath+FILE_SEPERATOR+featureName+".java").exists()) {
			
				//System.out.print(initConfig.getServices().getNamespaces());
			List<ProofHandler> proofList = loadInKeY(new File(metaPath+FILE_SEPERATOR+featureName+".java"));
			for(ProofHandler proofHandler : proofList) {
				KeYEnvironment<?> environment = proofHandler.getEnvironment();
				Contract contract = proofHandler.getContract();
				String name = contract.getTarget().toString();
				if(name.contains(methodName+"_BankAccount")) {
					return environment.getInitConfig().getServices().getJavaModel();
				}						
				
			}	
		}
		return null;
	}
}
