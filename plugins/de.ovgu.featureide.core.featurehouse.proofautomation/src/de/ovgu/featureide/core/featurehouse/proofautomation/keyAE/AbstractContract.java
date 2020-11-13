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
package de.ovgu.featureide.core.featurehouse.proofautomation.keyAE;

import java.io.File;
import java.util.HashMap;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.macros.CompleteAbstractProofMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.util.MiscTools;

/**
 * AbstractContract is used for proofing in the abstract contracts with metaproducts and reuse
 * 
 * @author marlen
 */
public class AbstractContract extends KeyHandler{
	
	/**
	 * Starts the proof 
	 */
	public void startAbstractProof(ProofHandler proofHandler,int maxRuleApplication, StrategyProperties sp) {	
		try {
			KeYEnvironment<?> environment = proofHandler.getEnvironment();
			Contract contract = proofHandler.getContract();
			ProofOblInput input = contract.createProofObl(environment.getInitConfig(), contract);
				
			Proof proof = environment.createProof(input);
			
			// Set proof strategy options
	        ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
	        HashMap<String,String> choices = proof.getSettings().getChoiceSettings().getDefaultChoices();
	        choices.putAll(MiscTools.getDefaultTacletOptions());
	        choiceSettings.setDefaultChoices(choices);
			proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
			
			// Make sure that the new options are used
			ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(maxRuleApplication);
			ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(sp);
			proof.getSettings().getStrategySettings().setMaxSteps(maxRuleApplication);
	        proof.setActiveStrategy(proof.getServices().getProfile().getDefaultStrategyFactory().create(proof, sp));
	        ProofControl proofControl = environment.getUi().getProofControl();
			int previousNodes;
			do{
				previousNodes = proof.countNodes();
				proofControl.runMacro(proof.root(), new CompleteAbstractProofMacro(), null);
				proofControl.waitWhileAutoMode();				
			}while(proof.countNodes()==previousNodes);
	        if(proof.openGoals().isEmpty()){	        	
	        	proofHandler.setClosed(true);	        	
	        }	
	        proofHandler.setProof(proof);
	        proofHandler.setStatistics();
	        environment.dispose();
		} 
		catch (ProofInputException e) {
            e.printStackTrace();
		}
	}
	
	/**
	 * Starts a Proof for the Metaproduct Verification with reuseProof for reuse and prepared Settings
	 * @param proofHandler
	 * @param reuseProof
	 * @param sp
	 * @param maxRuleApplication
	 * @param savePath
	 * @return
	 */
	public boolean startMetaProductProof(ProofHandler proofHandler,File reuseProof, StrategyProperties sp, int maxRuleApplication, String savePath) {
		boolean reusedAProof = false;
		try {
			KeYEnvironment<?> environment = proofHandler.getEnvironment();
			Contract contract = proofHandler.getContract();
			ProofOblInput input = contract.createProofObl(environment.getInitConfig(), contract);
			
			Proof proof = environment.createProof(input);
	        ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
			HashMap<String,String> choices = proof.getSettings().getChoiceSettings().getDefaultChoices();
	        choices.put("assertions", "assertions:safe");
	        choices.putAll(MiscTools.getDefaultTacletOptions());
	        choiceSettings.setDefaultChoices(choices);
	        
	        if(reuseProof!=null){
		        if(reuseProof.getName().endsWith(".proof")){
		        	UserInterfaceControl userInterface = new DefaultUserInterfaceControl(null);
		        	KeYEnvironment<UserInterfaceControl> keYEnvironment = null;
		            try {
		            	AbstractProblemLoader loader = userInterface.load(null, reuseProof, null, null, null, null, false);
		            	InitConfig initConfig = loader.getInitConfig();
		            	keYEnvironment = new KeYEnvironment<>(userInterface, initConfig, loader.getProof(), loader.getProofScript(), loader.getResult());
		            	Proof proof2 = keYEnvironment.getLoadedProof();
	          	
		            	keYEnvironment.getProofControl().runMacro(proof2.root(),new CompleteAbstractProofMacro(), null);
		            	keYEnvironment.getProofControl().waitWhileAutoMode();
		            	reusedAProof = true;
						proofHandler.setProof(proof2);
					} catch (ProblemLoaderException e) {
						System.out.println("Loading the File " + reuseProof.toString() + " failed in Method startMetaProductProof");
						e.printStackTrace();
					}	
		            
		            File reusedProof = proofHandler.saveProof(savePath);
	            	try {
						environment.load(reusedProof);
					} catch (ProblemLoaderException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
	            	reusedProof.delete();
	            	proofHandler.setReusedStatistics();
		        	
		        }
		        proof = proofHandler.getProof();
		        environment.dispose();
		       System.out.println("Reused: "+proofHandler.getProof().name() +"\n"+ proofHandler.getProof().getStatistics());
		    }
	        
	        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(maxRuleApplication);
	        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(sp);
	        proof.getSettings().getStrategySettings().setMaxSteps(maxRuleApplication);
	        proof.setActiveStrategy(environment.getProfile().getDefaultStrategyFactory().create(proof, sp));

	        while(!proof.openEnabledGoals().isEmpty() && goalHasApplicableRules(proof)){
	        	int previousNodes = proof.countNodes();
	        	environment.getProofControl().startAndWaitForAutoMode(proof);
	        	if(proof.countNodes()==previousNodes){
	        		break;
	        	}
	        }
	        proofHandler.setClosed(true);

	        if(!proof.openGoals().isEmpty()){
	        	System.out.println(proofHandler.getTargetName()+proofHandler.getTypeName()+" was not closed");
	        	proofHandler.setClosed(false);
	        }
	        proofHandler.setProof(proof);
	        proofHandler.setStatistics();
	        
	        System.out.println("Actual: " + proof.getStatistics());
	      
		}
		catch (ProofInputException e) {
			e.printStackTrace();
		}
		return reusedAProof;
	}
	
	
	/**
	 * @param oldPartialProof
	 * @param maxRuleApplication
	 * @param defaultSettingsForFeatureStub
	 */
	public void replayFeatureStubProof(ProofHandler proofHandler,File oldPartialProof, String savePath, int maxRuleApplication,
			StrategyProperties defaultSettingsForFeatureStub) {
		
			boolean reusedAProof = false;
		try{
			KeYEnvironment<?> environment = proofHandler.getEnvironment();
			Contract contract = proofHandler.getContract();
			ProofOblInput input = contract.createProofObl(environment.getInitConfig(), contract);
	
			Proof proof = environment.getUi().createProof(environment.getInitConfig(), input);
			HashMap<String,String> choices = proof.getSettings().getChoiceSettings().getDefaultChoices();
	        choices.put("assertions", "assertions:safe");
	        ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
	        choiceSettings.setDefaultChoices(choices);
	        if(oldPartialProof!=null){
		        if(oldPartialProof.getName().endsWith(".proof")){
		        	UserInterfaceControl userInterface = new DefaultUserInterfaceControl(null);
		        	KeYEnvironment<UserInterfaceControl> keYEnvironment = null;
		            try {
		            	AbstractProblemLoader loader = userInterface.load(null, oldPartialProof, null, null, null, null, false);
		            	InitConfig initConfig = loader.getInitConfig();
		            	keYEnvironment = new KeYEnvironment<>(userInterface, initConfig, loader.getProof(), loader.getProofScript(), loader.getResult());
		            	Proof proof2 = keYEnvironment.getLoadedProof();
		            	
		            	keYEnvironment.getProofControl().runMacro(proof2.root(),new CompleteAbstractProofMacro(), null);
		            	keYEnvironment.getProofControl().waitWhileAutoMode();
		            	reusedAProof = true;
		            	proofHandler.setProof(proof2);
					} catch (ProblemLoaderException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}	
		            
		            File reusedProof = proofHandler.saveProof(savePath);
	            	try {
						environment.load(reusedProof);
					} catch (ProblemLoaderException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
	            	reusedProof.delete();
	            	
	            	proofHandler.setReusedStatistics();
		        	
		        }
	        }
	    }catch (Exception e) {
			e.printStackTrace();
		}
	}

	/**
	 * 
	 * @param proof
	 * @return
	 */
	public static boolean goalHasApplicableRules(Proof proof){
		ImmutableList<Goal> goals = proof.openGoals();
		for(Goal g: goals){
			if(SymbolicExecutionUtil.hasApplicableRules(g)){
				return true;
			}
		}
		return false;
	}
}
