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
import de.ovgu.featureide.core.featurehouse.proofautomation.builder.BuilderUtil;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.control.UserInterfaceControl;
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
import de.uka.ilkd.key.util.MiscTools;

/**
 * the default keY prover is used to for proving 
 * 
 * @author marlen
 */
public class DefaultKeY extends KeyHandler{
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
	
	/**
	 * @param account
	 * @param maxRuleApplication
	 * @param defaultSettingsForMetaproduct
	 */
	public boolean startMetaProductProof(ProofHandler proofHandler,File reuseProof, int maxRuleApplication,
			StrategyProperties sp,String savePath, String analyseType) {
		boolean reusedAProof = false;
		System.out.println("Start startMetaProductProof of target: " + proofHandler.getTargetName());

		KeYEnvironment<?> environment = proofHandler.getEnvironment();
	    Contract contract = proofHandler.getContract();
		ProofOblInput input = contract.createProofObl(environment.getInitConfig(), contract);	
		try {
			proofHandler.proof = environment.createProof(input);
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
        proofHandler.proof.setActiveStrategy(environment.getProfile().getDefaultStrategyFactory().create(proofHandler.proof, sp));
        ProofControl proofControl = environment.getProofControl();	
		try{	    
 	        if(reuseProof!=null){
	        	if(reuseProof.getName().endsWith(".proof")){
	        		replaceJavaSource(reuseProof);
	        		UserInterfaceControl userInterface = new DefaultUserInterfaceControl(null);
	    			AbstractProblemLoader loader = userInterface.load(null, reuseProof, null, null, null, null, false);
					InitConfig initConfig = loader.getInitConfig();	
					environment = new KeYEnvironment<>(userInterface, initConfig, loader.getProof(), loader.getProofScript(), loader.getResult());
					proofHandler.proof = environment.getLoadedProof();
	            	proofControl = environment.getProofControl();
	            	proofControl.startAndWaitForAutoMode(proofHandler.proof);
	            	reusedAProof = true;
	            	
		            System.out.println("Reused: "+proofHandler.getTargetName()+"\n"+ proofHandler.getProof().getStatistics());
		            proofHandler.setReusedStatistics();
		            File reusedProof = null;
		            if(analyseType.equals("Fefalution")) {		            	
		            	reusedProof = proofHandler.saveProof(reuseProof.getParentFile().getAbsolutePath());
		            	replaceJavaSource(reusedProof);
		            }else {
		            	reusedProof = proofHandler.saveProof(savePath);
		            }
		            
	    			loader = userInterface.load(null, reuseProof, null, null, null, null, false);
					initConfig = loader.getInitConfig();	
					environment = new KeYEnvironment<>(userInterface, initConfig, loader.getProof(), loader.getProofScript(), loader.getResult());
	            	reusedProof.delete();
	            	proofHandler.proof = environment.getLoadedProof();
	            	proofControl = environment.getProofControl();


	        }
	        	proofHandler.proof = environment.getUi().createProof(environment.getInitConfig(), input);
	        	proofHandler.proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
	        	ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(maxRuleApplication);
	        	ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(sp);
	        	proofHandler.proof.getSettings().getStrategySettings().setMaxSteps(maxRuleApplication);
	        	proofHandler.proof.setActiveStrategy(proofHandler.proof.getServices().getProfile().getDefaultStrategyFactory().create(proofHandler.proof, sp));
		        
	        int previousNodes;	
	        do{
				previousNodes = proofHandler.proof.countNodes();	
				proofControl.startAndWaitForAutoMode(proofHandler.proof);
            	proofHandler.setProof(proofHandler.proof);
	        	System.out.println("Open goals of " + proofHandler.getTargetName()+" in " +proofHandler.getTypeName()+" has " + proofHandler.proof.openGoals().size() +" open Goals" );

				}while(proofHandler.proof.countNodes()==previousNodes);
	        
		        if(proofHandler.proof.openGoals().isEmpty()){
		        	System.out.println("Metaproductproof of " + proofHandler.getTargetName()+" in " +proofHandler.getTypeName()+" was not closed with " + proofHandler.proof.openGoals().size() +" open Goals");
		            proofHandler.setClosed(true);
		        }
        	}

		} catch (ProofInputException | ProblemLoaderException e) {
            System.out.println("Exception at '" + contract.getDisplayName() + "' of " + contract.getTarget() + ":");
            e.printStackTrace();
		}
		proofHandler.setProof(proofHandler.proof);
		proofHandler.setStatistics();
        System.out.println("Actual: "+ proofHandler.getTargetName() +"\n" + proofHandler.proof.getStatistics());

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
	            	replaceJavaSource(oldPartialProof);
	            	AbstractProblemLoader loader = userInterface.load(null, oldPartialProof, null, null, null, null, false);
	            	InitConfig initConfig = loader.getInitConfig();
	            	keYEnvironment = new KeYEnvironment<>(userInterface, initConfig, loader.getProof(), loader.getProofScript(), loader.getResult());
	            	proofHandler.proof = keYEnvironment.getLoadedProof();
	            	ProofControl proofControl = keYEnvironment.getProofControl();

	            	proofControl.startAndWaitForAutoMode(proofHandler.proof);
					reusedAProof = true;
	            	
				} catch (ProblemLoaderException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}	
	          //  savePath = oldPartialProof.getParentFile().getAbsolutePath();
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
            //	keYEnvironment.dispose();
	        }
        }
    }catch (Exception e) {
		e.printStackTrace();
	}
		}	

	/**
	 * replaces the javasouce in the proof-File with an empty string, because of a bug in KeY.
	 * bug:when loading a proof-File it adds the Path of the folder of the file in front of the javasource-String 
	 * @param proof
	 */
	private static void replaceJavaSource(File proof){
		String FILE_SEPERATOR = System.getProperty("file.separator");
		StringBuffer sbuffer = new StringBuffer();
		try {
			BufferedReader bReader = new BufferedReader(new FileReader(proof));
            String line = bReader.readLine();
            while(line != null) {
            	if(line.startsWith("\\javaSource")) {
            		line = "\\javaSource \"\";";
            	}
            	sbuffer.append(line + System.getProperty("line.separator"));
                line = bReader.readLine();
            }
            bReader.close();
        } catch(IOException e) {
            e.printStackTrace();
        }
        BuilderUtil.rewriteFile(sbuffer,proof);
	}
}
