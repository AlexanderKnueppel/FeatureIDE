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
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.key_project.util.collection.ImmutableSet;

import bibliothek.gui.dock.themes.StationCombinerValue;
import de.ovgu.featureide.core.featurehouse.proofautomation.configuration.Configuration;
import de.ovgu.featureide.core.featurehouse.proofautomation.key.AutomatingProof;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.gui.ClassTree;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IObserverFunction;
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
import de.uka.ilkd.key.util.KeYTypeUtil;
import de.uka.ilkd.key.util.MiscTools;

/**
 * KeYhandler handels all the action that have to do directly with key
 * 
 * @author marlen
 */
public class KeyHandler {
	

	public static void main(String[] args) {
		loadInKeY(new File("/mnt/54AFF99F466B2AED/Informatik/Masterarbeit/Latex/Eval/features/DailyLimit"));
	}
	
	/**
	 * @param oldPartialProof
	 * @param maxRuleApplication
	 * @param defaultSettingsForFeatureStub
	 */
	public static void startAbstractExcutionProof(ProofHandler proofHandler, int maxRuleApplication, StrategyProperties sp) {
		
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
	
				proofControl.waitWhileAutoMode();
	
			}while(proof.countNodes()==previousNodes);
	        if(proof.openGoals().isEmpty()){
	            System.out.println("Contract '" + contract.getDisplayName() + "' of " + contract.getTarget() + " is " + (proofHandler.isClosed() ? "verified" : "still open") + ".");
	            proofHandler.setClosed(true);
	        }
		} catch (ProofInputException e) {
            System.out.println("Exception at '" + contract.getDisplayName() + "' of " + contract.getTarget() + ":");
            e.printStackTrace();
		}
		proofHandler.setStatistics();
		
	}
	
	/**
	 * Loads a Proof-File into key, sorts and cleans the contracts and saves the Proofs into
	 * a List with ProofHandler objects
	 * @param location
	 * @return
	 */	
	public static List<ProofHandler> loadInKeY(File location) {
		List<ProofHandler> proofs =  new LinkedList<ProofHandler>();
		try {
			//removes existing Settings
			if (!ProofSettings.isChoiceSettingInitialised()) {
	            KeYEnvironment<?> env = KeYEnvironment.load(location, null, null, null);
	            env.dispose();
	         }
			ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
			HashMap<String,String> choices =  choiceSettings.getDefaultChoices();
			choices.putAll(MiscTools.getDefaultTacletOptions());
			choices.put("assertions", "assertions:safe");
			choiceSettings.setDefaultChoices(choices);
			
            KeYEnvironment<?> env = KeYEnvironment.load(location, null, null, null);

            
            final List<Contract> proofContracts = new LinkedList<Contract>();
            Set<KeYJavaType> kjts = env.getJavaInfo().getAllKeYJavaTypes();
            
            //sort for size
	        final KeYJavaType[] kjtsarr = kjts.toArray(new KeYJavaType[kjts.size()]);
	        Arrays.sort(kjtsarr, new Comparator<KeYJavaType>() {
	            public int compare(KeYJavaType o1, KeYJavaType o2) {
	               return o1.getFullName().compareTo(o2.getFullName());
	            }
	         });
	        
            for (KeYJavaType type : kjtsarr) {
               if (!KeYTypeUtil.isLibraryClass(type)) {
                  ImmutableSet<IObserverFunction> targets = env.getSpecificationRepository().getContractTargets(type);
                  for (IObserverFunction target : targets) {
                     ImmutableSet<Contract> contracts = env.getSpecificationRepository().getContracts(type, target);
                     for (Contract contract : contracts) {
                    	 if(!type.getFullName().equals(Configuration.excludedClass)||!Configuration.excludeMain){
 	                		ProofHandler a = new ProofHandler(type.getFullName(), ClassTree.getDisplayName(env.getServices(), contract.getTarget()), contract.getDisplayName(), env, contract);
 	                		//Checking for dispatch and original contracts, that need to be deleted
 	                		if(!a.getTargetName().contains("dispatch")||Configuration.proveDispatcher){
 	                			if(!a.getTargetName().contains("_original_")||Configuration.proveOriginal){
 	                				proofs.add(a);
 	                			}
 	                			if(!Configuration.proveDispatcher&&Configuration.currentMetaproductwithDispatcher){
 	                				removeDispatcher(proofs);
 	                			}
 	                		}
 	                	}
                        proofContracts.add(contract);
                     }
                  }
               }
            }

		}catch (ProblemLoaderException e) {
	         System.out.println("Exception at '" + location + "':");
	         e.printStackTrace();
		}
		return proofs;
	}
	
	/**
	 * Removes unwanted dispatcher contracts
	 * @param proofs
	 */
	private static void removeDispatcher(List<ProofHandler> proofs){
		//pattern nameMethode_ contains
		List<ProofHandler> removeDispatcher = new LinkedList<ProofHandler>();
		for(ProofHandler a: proofs){
			for(ProofHandler b: proofs){
				String aNameWithoutBrackets = a.getTargetName().replaceAll("\\(.*\\)", "");
				if(b.getTypeName().equals(a.getTypeName())&&a!=b){
					if(b.getTargetName().contains(aNameWithoutBrackets+"_")){
						removeDispatcher.add(a);
					}
				}
			}
		}
		proofs.removeAll(removeDispatcher);
	}


}