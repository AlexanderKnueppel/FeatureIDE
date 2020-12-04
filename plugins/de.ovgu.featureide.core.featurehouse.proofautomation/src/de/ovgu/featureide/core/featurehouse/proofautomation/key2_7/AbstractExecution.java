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
import java.util.List;

import de.ovgu.featureide.core.featurehouse.proofautomation.builder.BuilderUtil;
import de.ovgu.featureide.core.featurehouse.proofautomation.filemanagement.FileManager;
import de.ovgu.featureide.core.featurehouse.proofautomation.key.DefaultStrategies;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.macros.CompleteAbstractProofMacro;
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

/**
 * AbstractExcution is used to for proving 
 * 
 * @author marlen
 */
public class AbstractExecution extends KeyHandler{
	
	/** Initializes the abstract execution proof  
	 * @param oldPartialProof
	 * @param maxRuleApplication
	 * @param defaultSettingsForFeatureStub
	 */
	public void startAbstractProof(ProofHandler proofHandler, int maxRuleApplication, StrategyProperties sp) {
		
		KeYEnvironment<?> environment = proofHandler.getEnvironment();
		Proof proof = proofHandler.getProof();
		Contract contract = proofHandler.getContract();
		try{
			
		    ProofOblInput input = contract.createProofObl(environment.getInitConfig(), contract);
		    proof = environment.getUi().createProof(environment.getInitConfig(), input);

        	proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
        	ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(maxRuleApplication);
        	ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(sp);
        	proof.getSettings().getStrategySettings().setMaxSteps(maxRuleApplication);
	        proof.setActiveStrategy(proof.getServices().getProfile().getDefaultStrategyFactory().create(proof, sp));
			ProofControl proofControl = environment.getUi().getProofControl();
			int previousNodes;
			do{
				previousNodes = proof.countNodes();
	
				proofControl.startAndWaitForAutoMode(proof);
	
			}while(proof.countNodes()==previousNodes);
	        if(proof.openGoals().isEmpty()){
	            System.out.println("Contract '" + contract.getDisplayName() + "' of " + contract.getTarget() + " is " + (proofHandler.isClosed() ? "verified" : "still open") + ".");
	            proofHandler.setClosed(true);
	        }
	        proofHandler.setProof(proof);
		} catch (ProofInputException e) {
            System.out.println("Exception at '" + contract.getDisplayName() + "' of " + contract.getTarget() + ":");
            e.printStackTrace();
		}
		proofHandler.setStatistics();
		
	}
	
	/**
	 * @param account
	 * @param maxRuleApplication
	 * @param defaultSettingsForMetaproduct
	 */
	public static void startMetaProductProof(ProofHandler proofHandler,File reuseProof, int maxRuleApplication,
			StrategyProperties sp,String savePath, String analyseType) {
		boolean reusedAProof = false;
		KeYEnvironment<?> environment = proofHandler.getEnvironment();
		Proof proof = proofHandler.getProof();
		Contract contract = proofHandler.getContract();
		ProofOblInput input = contract.createProofObl(environment.getInitConfig(), contract);
		ProofControl proofControl = environment.getUi().getProofControl();
		
		try{				    
 
	        if(reuseProof!=null){
	        	if(reuseProof.getName().endsWith(".proof")){
	        		UserInterfaceControl userInterface = new DefaultUserInterfaceControl(null);
	    			AbstractProblemLoader loader = userInterface.load(null, reuseProof, null, null, null, null, false);
					InitConfig initConfig = loader.getInitConfig();	
					environment = new KeYEnvironment<>(userInterface, initConfig, loader.getProof(), loader.getProofScript(), loader.getResult());
	            	proof = environment.getLoadedProof();
	            	proofControl = environment.getProofControl();
	            	proofControl.startAndWaitForAutoMode(proof);
	            	reusedAProof = true;
	            	
		            proofHandler.setProof(proof);
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
	            	proof = environment.getLoadedProof();
	            	proofControl = environment.getProofControl();


	        }
			    proof = environment.getUi().createProof(environment.getInitConfig(), input);
	        	proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
	        	ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(maxRuleApplication);
	        	ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(sp);
	        	proof.getSettings().getStrategySettings().setMaxSteps(maxRuleApplication);
		        proof.setActiveStrategy(proof.getServices().getProfile().getDefaultStrategyFactory().create(proof, sp));
		        
	        int previousNodes;	
	        do{
				previousNodes = proof.countNodes();	
				proofControl.startAndWaitForAutoMode(proof);
	
				}while(proof.countNodes()==previousNodes);
		        if(proof.openGoals().isEmpty()){
		            System.out.println("Contract '" + contract.getDisplayName() + "' of " + contract.getTarget() + " is " + (proofHandler.isClosed() ? "verified" : "still open") + ".");
		            proofHandler.setClosed(true);
		        }
        	}

		} catch (ProofInputException | ProblemLoaderException e) {
            System.out.println("Exception at '" + contract.getDisplayName() + "' of " + contract.getTarget() + ":");
            e.printStackTrace();
		}
		proofHandler.setProof(proof);
		proofHandler.setStatistics();
	}
	
	public void replayFeatureStubProof(ProofHandler proofHandler,File oldPartialProof, String savePath, int maxRuleApplication,
			StrategyProperties defaultSettingsForFeatureStub) {
		System.out.println("Start replayFeatureStubProof of target: " + proofHandler.getTargetName());
		boolean reusedAProof = false;
		System.out.println(oldPartialProof.getAbsolutePath());
	try{
		KeYEnvironment<?> keYEnvironment = proofHandler.getEnvironment();
		Contract contract = proofHandler.getContract();
		ProofOblInput input = contract.createProofObl(keYEnvironment.getInitConfig(), contract);

		Proof proof = keYEnvironment.createProof(input);
		HashMap<String,String> choices = proof.getSettings().getChoiceSettings().getDefaultChoices();
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
	            	proof = keYEnvironment.getLoadedProof();
	            	ProofControl proofControl = keYEnvironment.getProofControl();

					proofControl.waitWhileAutoMode();
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
