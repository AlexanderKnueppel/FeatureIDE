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

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
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
	 * @param account
	 * @param maxRuleApplication
	 * @param defaultSettingsForMetaproduct
	 */
	public static void startMetaProductProof(ProofHandler account, int maxRuleApplication,
			StrategyProperties defaultSettingsForMetaproduct) {
		// TODO Auto-generated method stub
		
	}

	
}
