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
package de.ovgu.featureide.core.featurehouse.proofautomation.model;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.core.featurehouse.proofautomation.builder.BuilderUtil;
import de.ovgu.featureide.core.featurehouse.proofautomation.builder.FeatureStubBuilder;
import de.ovgu.featureide.core.featurehouse.proofautomation.builder.MetaProductBuilder;
import de.ovgu.featureide.core.featurehouse.proofautomation.excel.ExcelManager;
import de.ovgu.featureide.core.featurehouse.proofautomation.filemanagement.FileManager;
import de.ovgu.featureide.core.featurehouse.proofautomation.key.AutomatingProject;
import de.ovgu.featureide.core.featurehouse.proofautomation.key.AutomatingProof;

/**
 * TODO description
 * 
 * @author Stefanie
 */
public class SingleProject extends Evaluation{
	private List<AutomatingProof> proofList = new LinkedList<AutomatingProof>();
	private static final String FILE_SEPERATOR = System.getProperty("file.separator");
	private BufferedWriter bw;
	
	public SingleProject(File f){
		this.toEvaluate = f;
	}
	
	public List<AutomatingProof> getProofList(){
		return proofList;
	}
	
	public void performEvaluation(){
		System.out.println("This should perform a single Project Evaluation");
//		FeatureStubsGenerator fsg = new FeatureStubsGenerator(featureProject);
//		fsg.generate();
//		buildMetaproduct(featureProject);
		File transactionAccount = new File(toEvaluate.getAbsolutePath()+FILE_SEPERATOR+"featurestub"+FILE_SEPERATOR+"Transaction"+FILE_SEPERATOR+"Account.java");
		File lockAccount = new File(toEvaluate.getAbsolutePath()+FILE_SEPERATOR+"featurestub"+FILE_SEPERATOR+"Lock"+FILE_SEPERATOR+"Account.java");
		File metap = new File(toEvaluate.getAbsolutePath()+FILE_SEPERATOR+"src"+FILE_SEPERATOR+"Account.java");
		FeatureStubBuilder.prepareForVerification(transactionAccount,lockAccount);
		BuilderUtil.removeBracketsOfVar(metap, "lock");
		AutomatingProject a = new AutomatingProject();
		a.performFeaturestubVerification(toEvaluate);
		FileManager.copySavedProofsToPartialProofs(toEvaluate);
		MetaProductBuilder.preparePartialProofs(toEvaluate);
		a.performMetaproductVerification(toEvaluate);
	}
	
	public void updateSum(AutomatingProof a){
		nodeSum+=a.getNodes();
		branchesSum+=a.getBranches();
		appliedRulesSum+=a.getAppliedRules();
		automodeTimeSum+=a.getTime();
	}
	
	public void createXLS(){
		ExcelManager.generateSingleProjectXLS(this);;
	}
}
