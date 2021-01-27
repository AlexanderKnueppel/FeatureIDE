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
package de.ovgu.featureide.core.featurehouse.proofautomation.verification;

import java.io.File;

import de.ovgu.featureide.core.featurehouse.proofautomation.builder.MetaProductBuilder;
import de.ovgu.featureide.core.featurehouse.proofautomation.builder.MetaProductBuilderNonRigid;
import de.ovgu.featureide.core.featurehouse.proofautomation.configuration.Configuration;
import de.ovgu.featureide.core.featurehouse.proofautomation.filemanagement.FileManager;
import de.ovgu.featureide.core.featurehouse.proofautomation.key.KeyHandler;
import de.ovgu.featureide.core.featurehouse.proofautomation.key.Non_Rigid;
import de.uka.ilkd.key.java.reference.ThisConstructorReference;

/**
 *  Class for verification of approach 1 Fefalution + Family Proof Replay
 * 
 * @author Marlen Herter-Bernier
 */
public class FefalutionFamilyProofReplay extends AbstractVerification{
	private int maxRuleApplication = Configuration.maxRuleApplication; // sets the maximal number of rules to be applicated on one proof
	public static final FefalutionFamilyProofReplay FAMILY_PROOF_REPLAY = new FefalutionFamilyProofReplay();
	
	public static FefalutionFamilyProofReplay getInstance() {
		return FAMILY_PROOF_REPLAY;
	}
	
	private FefalutionFamilyProofReplay() {
		keyHandler = new Non_Rigid();
		method="Non Rigid";
	}
	public static void  main(String[] args){
		File locFile = new File("/mnt/54AFF99F466B2AED/Informatik/Masterarbeit/eval2/Sandbox/BankAccountv1");
		File evalPathFile  =new File("/mnt/54AFF99F466B2AED/Informatik/Masterarbeit/eval2/Sandbox/Evaluation/2021-01-04 13-32-35/1 Fefalution + Family Proof Replay/BankAccountv1");

		FileManager.copySavedProofsToPartialProofs(evalPathFile);
		MetaProductBuilderNonRigid.preparePartialProofs(locFile,evalPathFile);
		getInstance().performMetaproductVerification(locFile, evalPathFile);
/*
		getInstance().performVerification(locFile, evalPathFile);*/
		
	}
	

	/**
	 * Performs the evaluation
	 * @param loc
	 */
	public void performVerification(File loc, File evalPath){

		boolean firstVersion = loc.getName().contains("1");
		if(!firstVersion){
			FileManager.reuseFeaturestub(evalPath, loc);
		}
		performFeaturestubVerification(loc,evalPath,firstVersion, true);
		FileManager.copySavedProofsToPartialProofs(evalPath);
		if(method.equals("Non Rigid")) {
			MetaProductBuilderNonRigid.preparePartialProofs(loc,evalPath);
		}else {
			MetaProductBuilder.preparePartialProofs(loc,evalPath);
		}		

		this.performMetaproductVerification(loc,evalPath);
	}
}