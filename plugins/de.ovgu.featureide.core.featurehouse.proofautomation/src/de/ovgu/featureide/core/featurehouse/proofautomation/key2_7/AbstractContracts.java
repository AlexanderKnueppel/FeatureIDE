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
package de.ovgu.featureide.core.featurehouse.proofautomation.key2_7;


import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.HashMap;

import org.key_project.util.collection.ImmutableList;

import de.ovgu.featureide.core.featurehouse.proofautomation.builder.BuilderUtil;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.macros.CompleteAbstractProofMacro;
import de.uka.ilkd.key.macros.ContinueAbstractProofMacro;
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
public class AbstractContracts extends KeyHandler{
	/**
	 * Starts the proof 
	 */
	public void startAbstractProof(ProofHandler proofHandler,int maxRuleApplication, StrategyProperties sp) {	
		try {
			KeYEnvironment<?> environment = proofHandler.getEnvironment();
			Contract contract = proofHandler.getContract();
			ProofOblInput input = contract.createProofObl(environment.getInitConfig(), contract);
			proofHandler.proof	= environment.createProof(input);
						
			// Set proof strategy options
	        ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
	        HashMap<String,String> choices = proofHandler.proof.getSettings().getChoiceSettings().getDefaultChoices();
	        choices.putAll(MiscTools.getDefaultTacletOptions());
	        choiceSettings.setDefaultChoices(choices);

	        proofHandler.proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
			
			// Make sure that the new options are used
			ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(maxRuleApplication);
			ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(sp);
			proofHandler.proof.getSettings().getStrategySettings().setMaxSteps(maxRuleApplication);
			proofHandler.proof.setActiveStrategy(proofHandler.proof.getServices().getProfile().getDefaultStrategyFactory().create(proofHandler.proof, sp));
	        
	        ProofControl proofControl = environment.getUi().getProofControl();
			int previousNodes;
			do{
				previousNodes = proofHandler.proof.countNodes();

				//proofControl.runMacro(proof.root(), new ContinueAbstractProofMacro(), null);

				proofControl.runMacro(proofHandler.proof.root(), new CompleteAbstractProofMacro(), null);
				proofControl.waitWhileAutoMode();

			}while(proofHandler.proof.countNodes()==previousNodes);
	        if(proofHandler.proof.openGoals().isEmpty()){
	        	System.out.println("Proof " +proofHandler.proof.name() + " was closed");
	        	proofHandler.setClosed(true);	        	
	        }	
	      //  proofHandler.setProof(proof);
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
	@Override
	public boolean startMetaProductProof(ProofHandler proofHandler,File reuseProof, StrategyProperties sp, int maxRuleApplication, String savePath) {
		boolean reusedAProof = false;
		System.out.println("Start startMetaProductProof of target: " + proofHandler.getTargetName());
	
		KeYEnvironment<?> keYEnvironment = proofHandler.getEnvironment();
	    Contract contract = proofHandler.getContract();
		ProofOblInput input = contract.createProofObl(keYEnvironment.getInitConfig(), contract);	
		try {
			proofHandler.proof = keYEnvironment.createProof(input);
		} catch (ProofInputException e1) {
			e1.printStackTrace();
		}
		 
        ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
		HashMap<String,String> choices = new HashMap<String,String>();
        choices.put("assertions", "assertions:safe");
        choices.putAll(MiscTools.getDefaultTacletOptions());
        choiceSettings.setDefaultChoices(choices);
        
		ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(maxRuleApplication);
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(sp);
        proofHandler.proof.getSettings().getStrategySettings().setMaxSteps(maxRuleApplication);
        proofHandler.proof.setActiveStrategy(keYEnvironment.getProfile().getDefaultStrategyFactory().create(proofHandler.proof, sp));
        ProofControl proofControl = keYEnvironment.getProofControl();	        
		 try {              	 
	        if(reuseProof!=null){
		        if(reuseProof.getName().endsWith(".proof")){
		        	UserInterfaceControl userInterface = new DefaultUserInterfaceControl(null);
	    			AbstractProblemLoader loader = userInterface.load(null, reuseProof, null, null, null, null, false);
					InitConfig initConfig = loader.getInitConfig();	
					
	            	keYEnvironment = new KeYEnvironment<>(userInterface, initConfig, loader.getProof(), loader.getProofScript(), loader.getResult());
	            	proofHandler.proof = keYEnvironment.getLoadedProof();
	            	proofControl = keYEnvironment.getProofControl();
	            	
	            	proofControl.runMacro(proofHandler.proof.root(),new CompleteAbstractProofMacro(), null);

	            	//proofControl.runMacro(proof.root(),new ContinueAbstractProofMacro(), null);
	            	proofControl.waitWhileAutoMode();
	            	reusedAProof = true;

		            //save Proof and load it again for further use
		            File reusedProof = proofHandler.saveProof(savePath);
	    			loader = userInterface.load(null, reuseProof, null, null, null, null, false);
					reusedProof.delete();
					
	    			initConfig = loader.getInitConfig();	
	            	keYEnvironment = new KeYEnvironment<>(userInterface, initConfig, loader.getProof(), loader.getProofScript(), loader.getResult());
	            	proofHandler.proof = keYEnvironment.getLoadedProof();
	            	
		            System.out.println("Reused: "+proofHandler.getTargetName()+"\n"+ proofHandler.getProof().getStatistics());
		            proofHandler.setReusedStatistics();
		            System.out.println("Open goals of " + proofHandler.getTargetName()+" in " +proofHandler.getTypeName()+" has " + proofHandler.proof.openGoals().size() +" open Goals" );
		            
	            	proofControl = keYEnvironment.getProofControl();
	            	//proofControl.runMacro(proof.root(),new CompleteAbstractProofMacro(), null);
		        }      
	        }	        
               
	        while(!proofHandler.proof.openEnabledGoals().isEmpty() && goalHasApplicableRules(proofHandler.proof)){	        	
	        	int previousNodes = proofHandler.proof.countNodes();
	        	proofControl.runMacro(proofHandler.proof.root(),new ContinueAbstractProofMacro(), null);
	        //	proofControl.runMacro(proof.root(),new CompleteAbstractProofMacro(), null);
            	proofControl.waitWhileAutoMode();
            	//proofHandler.setProof(proof);
	        	System.out.println("Open goals of " + proofHandler.getTargetName()+" in " +proofHandler.getTypeName()+" has " + proofHandler.proof.openGoals().size() +" open Goals" );

	        	if(proofHandler.proof.countNodes()==previousNodes){
	        		break;
	        	}
	        }
	        proofHandler.setClosed(true);

	        if(!proofHandler.proof.openGoals().isEmpty()){
	        	System.out.println("Metaproductproof of " + proofHandler.getTargetName()+" in " +proofHandler.getTypeName()+" was not closed with " + proofHandler.proof.openGoals().size() +" open Goals");
	        	proofHandler.setClosed(false);
	        }
	      //.setProof(proof);
	        proofHandler.setStatistics();
	        
	        System.out.println("Actual: "+ proofHandler.getTargetName()+" has " + proofHandler.proof.openGoals().size() +" open Goals" +"\n" + proofHandler.proof.getStatistics());
	        }
		catch (ProblemLoaderException e) {
			// TODO Auto-generated catch block
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
		System.out.println("Start replayFeatureStubProof of target: " + proofHandler.getTargetName());
			boolean reusedAProof = false;
			System.out.println(oldPartialProof.getAbsolutePath());
		try{
			KeYEnvironment<?> keYEnvironment = proofHandler.getEnvironment();
			Contract contract = proofHandler.getContract();
			ProofOblInput input = contract.createProofObl(keYEnvironment.getInitConfig(), contract);
	
			proofHandler.proof = keYEnvironment.createProof(input);
			HashMap<String,String> choices = proofHandler.proof.getSettings().getChoiceSettings().getDefaultChoices();
	        choices.put("assertions", "assertions:safe");
	        ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
	        choiceSettings.setDefaultChoices(choices);
	        
	        if(oldPartialProof!=null){
		        if(oldPartialProof.getName().endsWith(".proof")){
		        	UserInterfaceControl userInterface = new DefaultUserInterfaceControl(null);
		            try {
		            	AbstractProblemLoader loader = userInterface.load(null, oldPartialProof, null, null, null, null, false);
		            	InitConfig initConfig = loader.getInitConfig();
		            	keYEnvironment = new KeYEnvironment<>(userInterface, initConfig, loader.getProof(), loader.getProofScript(), loader.getResult());
		            	proofHandler.proof = keYEnvironment.getLoadedProof();
		            	ProofControl proofControl = keYEnvironment.getProofControl();
		            	
		            	//proofControl.runMacro(proof.root(),new ContinueAbstractProofMacro(), null);
						proofControl.runMacro(proofHandler.proof.root(), new CompleteAbstractProofMacro(), null);
						proofControl.waitWhileAutoMode();
						reusedAProof = true;
		            	
					} catch (ProblemLoaderException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}	
		          //  savePath = oldPartialProof.getParentFile().getAbsolutePath();
		            File reusedProof = proofHandler.saveProof(savePath);
	            	try {	            		
	            		keYEnvironment.load(reusedProof);
						proofHandler.setProof(keYEnvironment.getLoadedProof());
					} catch (ProblemLoaderException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
	            	reusedProof.delete();	 
	            	proofHandler.setReusedStatistics();	
	            	keYEnvironment.dispose();
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
