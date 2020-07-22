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
package testbench;

import java.io.File;
import java.util.Date;
import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.core.featurehouse.proofautomation.builder.MetaProductBuilder;
import de.ovgu.featureide.core.featurehouse.proofautomation.builder.projectWorker;
import de.ovgu.featureide.core.featurehouse.proofautomation.configuration.Configuration;
import de.ovgu.featureide.core.featurehouse.proofautomation.filemanagement.FileManager;
import de.ovgu.featureide.core.featurehouse.proofautomation.key.AutomatingProof;

/**
 * TODO description
 * 
 * @author User
 */
public class Fefalution {
	private static final String FILE_SEPERATOR = System.getProperty("file.separator");
	private static final String APPROACH_NAME = "Fefalution";
	private File bankaccountDir = null;
	private File statistics = null;
	//private List<AutomatingProof> proofList; //contains all proofs of the current project
	//private List<AutomatingProof> phase1ProofList = new LinkedList<AutomatingProof>();
	//private List<AutomatingProof> proofListWithPhase1And2 = new LinkedList<AutomatingProof>();
	private int maxRuleApplication = Configuration.maxRuleApplication; // sets the maximal number of rules to be applicated on one proof
	
	public Fefalution(File pathToBankaccount, int versionOfBankaccount, String pathToEvaluation) {
		
	}
	
	public Fefalution(File pathToBankaccount){
		Date date = new Date();
		File dateDir = FileManager.createDateDir(date, new File(pathToBankaccount.getParent()+FILE_SEPERATOR+FileManager.evaluationDir));
		File vaDir = FileManager.createDir(new File(dateDir+FILE_SEPERATOR+APPROACH_NAME));
		this.bankaccountDir = FileManager.createDir(new File(vaDir+FILE_SEPERATOR+pathToBankaccount.getName()));
		this.statistics = new File (bankaccountDir+FILE_SEPERATOR+"Evaluation-Fefalution-" + dateDir.getName() + ".xlsx");
		boolean newMetaproduct=true,featurestub=true;
		projectWorker.generateCodeForSingleProject(pathToBankaccount.getName(), featurestub, newMetaproduct);
	}
	
	public void performEvaluation() {
		Configuration.setCurrentMetaproductwithDispatcher(true);
	}
	
	
	private void prepare() {
		
	}
	
	private void performVerification(File bankAccountDir, File pathToEvaluation){
////		File transactionAccount = new File(loc.getAbsolutePath()+FILE_SEPERATOR+FileManager.featureStubDir+FILE_SEPERATOR+"Transaction"+FILE_SEPERATOR+"Account.java");
////		File lockAccount = new File(loc.getAbsolutePath()+FILE_SEPERATOR+FileManager.featureStubDir+FILE_SEPERATOR+"Lock"+FILE_SEPERATOR+"Account.java");
////		FeatureStubBuilder.prepareForVerification(transactionAccount,lockAccount);
//		boolean firstVersion = loc.getName().contains("1");
//		if(!firstVersion){
//			FileManager.reuseFeaturestub(evalPath, loc);
//		}
//		performFeaturestubVerification(loc,evalPath,firstVersion, false); //TODO run with false
//		FileManager.copySavedProofsToPartialProofs(evalPath);
//		MetaProductBuilder.preparePartialProofs(loc,evalPath);
////		
////		if(loc.getName().contains("5") || loc.getName().contains("6")) {
////			File acc = new File(loc.getAbsolutePath()+FILE_SEPERATOR+FileManager.metaproductDir+FILE_SEPERATOR+"Account.java");
////			BuilderUtil.fixUpdateLoggingInBA5BA6(acc);
////		}
//		performMetaproductVerification(loc,evalPath);
	}
}
