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

import java.io.File;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.key_project.util.collection.ImmutableSet;
import de.ovgu.featureide.core.featurehouse.proofautomation.configuration.Configuration;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.gui.ClassTree;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.MiscTools;

/**
 * KeYhandler handels all the action that have to do directly with key
 * 
 * @author marlen
 */
public abstract class KeyHandler {
	

	public void main(String[] args) {
		loadInKeY(new File("/mnt/54AFF99F466B2AED/Informatik/Masterarbeit/Latex/Eval/features/DailyLimit"));
	}
	

	/**
	 * Loads a Proof-File into key, sorts and cleans the contracts and saves the Proofs into
	 * a List with ProofHandler objects
	 * @param location
	 * @return
	 */	
	public List<ProofHandler> loadInKeY(File location) {
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


        	
            boolean skipLibraryClasses = true;
            final List<Contract> proofContracts = new LinkedList<Contract>();
            Set<KeYJavaType> kjts = env.getJavaInfo().getAllKeYJavaTypes();
			final Iterator<KeYJavaType> it = kjts.iterator();
	        while (it.hasNext()) {
		           KeYJavaType kjt = it.next();
		           if (!(kjt.getJavaType() instanceof ClassDeclaration || 
		                 kjt.getJavaType() instanceof InterfaceDeclaration) || 
		               (((TypeDeclaration)kjt.getJavaType()).isLibraryClass() && skipLibraryClasses)) {
		              it.remove();
		           }
		        }
            //sort for size
	        final KeYJavaType[] kjtsarr = kjts.toArray(new KeYJavaType[kjts.size()]);
	        Arrays.sort(kjtsarr, new Comparator<KeYJavaType>() {
	            public int compare(KeYJavaType o1, KeYJavaType o2) {
	               return o1.getFullName().compareTo(o2.getFullName());
	            }
	         });
	        
            for (KeYJavaType type : kjtsarr) {
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
	
	/**
	 * 
	 * @param proofHandler
	 * @param reuseProof
	 * @param sp
	 * @param maxRuleApplication
	 * @param savePath
	 * @return
	 */
	public boolean startMetaProductProof(ProofHandler proofHandler,File reuseProof,  StrategyProperties sp, int maxRuleApplication, String savePath) 
	{	
		return false;
	}


	/**
	 * @param maxRuleApplication
	 * @param defaultSettingsForFeatureStub
	 */
	public void startAbstractProof(ProofHandler proofHandler,int maxRuleApplication, StrategyProperties sp) {
	}
	
	/**
	 * 
	 * @param proofHandler
	 * @param oldPartialProof
	 * @param savePath
	 * @param maxRuleApplication
	 * @param defaultSettingsForFeatureStub
	 */
	public void replayFeatureStubProof(ProofHandler proofHandler,File oldPartialProof, String savePath, int maxRuleApplication,
			StrategyProperties defaultSettingsForFeatureStub) {	}

}
