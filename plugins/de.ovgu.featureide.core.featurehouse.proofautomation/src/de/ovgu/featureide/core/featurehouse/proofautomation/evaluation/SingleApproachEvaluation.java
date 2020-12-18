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
package de.ovgu.featureide.core.featurehouse.proofautomation.evaluation;

import java.io.File;
import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.core.featurehouse.proofautomation.builder.FeatureStubBuilder;
import de.ovgu.featureide.core.featurehouse.proofautomation.configuration.Configuration;
import de.ovgu.featureide.core.featurehouse.proofautomation.excel.ExcelManager2;
import de.ovgu.featureide.core.featurehouse.proofautomation.filemanagement.FileManager;
import de.ovgu.featureide.core.featurehouse.proofautomation.key2_7.AbstractContracts;
import de.ovgu.featureide.core.featurehouse.proofautomation.key2_7.DefaultKeY;
import de.ovgu.featureide.core.featurehouse.proofautomation.key2_7.KeyHandler;
import de.ovgu.featureide.core.featurehouse.proofautomation.key2_7.ProofHandler;
import de.ovgu.featureide.core.featurehouse.proofautomation.statistics.ProofInformation;
import de.ovgu.featureide.core.featurehouse.proofautomation.verification.AbstractVerification;
import de.ovgu.featureide.core.featurehouse.proofautomation.verification.ConcreteContracts;
import de.ovgu.featureide.core.featurehouse.proofautomation.verification.Fefalution;
import de.ovgu.featureide.core.featurehouse.proofautomation.verification.FefalutionFamilyProofReplay;
import de.ovgu.featureide.core.featurehouse.proofautomation.verification.Metaproduct;
import de.ovgu.featureide.core.featurehouse.proofautomation.verification.MethodInling;
import de.ovgu.featureide.core.featurehouse.proofautomation.verification.ThuemEtAl;
import de.ovgu.featureide.core.featurehouse.proofautomation.verification.ThuemEtAlReuse;


/**
 * Represents a Evaluation over one approach
 * 
 * @author marlen
 */
public class SingleApproachEvaluation extends Evaluation{
	public int failedProofs = 0;
	public int proofs = 0;
	private int evalVersion;
	private List<ProofInformation> phase1ProofList = new LinkedList<ProofInformation>();
	private List<ProofInformation> proofList = new LinkedList<ProofInformation>(); //contains all Automating proofs of this project
	private List<ProofInformation> proofList1And2Phase = new LinkedList<ProofInformation>();
public static void main(String[] args) {
	SingleApproachEvaluation s = new SingleApproachEvaluation(new File("/mnt/54AFF99F466B2AED/Informatik/Masterarbeit/AbstractExecution/account/BankAccountv1"), 1, 
			"/mnt/54AFF99F466B2AED/Informatik/Masterarbeit/AbstractExecution/account/Evaluation/BankAccountv1", "AbstractContract");
	s.performEvaluation();
}

	/**
	 * Constructor for execution in an verification approach
	 * Uses a given evaluatePath instead of a new
	 * @param f
	 * @param evalVersion
	 * @param evaluatePath
	 */
	public SingleApproachEvaluation(File f, int evalVersion, String evaluatePath, String method){
		super(f);
		System.out.println("Init SingleApproachEvaluation with Method " + method + "with Eval Version " + evalVersion);
		this.method = method;
		this.evaluatePath = FileManager.createDir(new File(evaluatePath));
		if(evalVersion>0){
			this.evalVersion = evalVersion;
		}
		else{
			this.evalVersion = getApproachVersion();
		}
		this.statistics = new File (evaluatePath+FILE_SEPERATOR+"Evaluation Results-VA" + this.evalVersion+".xlsx");
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.featurehouse.proofautomation.evaluation.Evaluation#performEvaluation()
	 */
	@Override
	public void performEvaluation() {
		if(evalVersion == 5||evalVersion == 6){
			Configuration.setCurrentMetaproductwithDispatcher(false);
		}else{
			Configuration.setCurrentMetaproductwithDispatcher(true);
		}
		FileManager.initFolders(evaluatePath, evalVersion);
		if(evalVersion == 1){
			
			File fstubPath = new File(toEvaluate.getAbsolutePath()+FILE_SEPERATOR+FileManager.featureStubDir);
			//Fix here instead of in performVa1 (i.e., before copy)
			File transactionAccount = new File(toEvaluate.getAbsolutePath()+FILE_SEPERATOR+FileManager.featureStubDir+FILE_SEPERATOR+"Transaction"+FILE_SEPERATOR+"Account.java");
			File lockAccount = new File(toEvaluate.getAbsolutePath()+FILE_SEPERATOR+FileManager.featureStubDir+FILE_SEPERATOR+"Lock"+FILE_SEPERATOR+"Account.java");
			FeatureStubBuilder.prepareForVerification(transactionAccount,lockAccount);

			
			//copy
			FileManager.copyCompleteFolderContent(fstubPath,new File(evaluatePath.getAbsolutePath()+FILE_SEPERATOR+FileManager.featureStubDir));

		}
		
		File metaproductPath = new File(toEvaluate.getAbsolutePath()+FILE_SEPERATOR+FileManager.metaproductDir);
		FileManager.copyCompleteFolderContent(metaproductPath,new File(evaluatePath.getAbsolutePath()+FILE_SEPERATOR+FileManager.metaproductDir));
		AbstractVerification abstractVerification = null;
		switch(evalVersion){
		case 1 :abstractVerification = FefalutionFamilyProofReplay.getInstance();
				break;				
		case 2 :abstractVerification = Metaproduct.getInstance();
				break;
		case 3 :abstractVerification = ConcreteContracts.getInstance();
				break;
		case 4 :abstractVerification = MethodInling.getInstance();
				break;
		case 5 :abstractVerification = ThuemEtAl.getInstance();
				break;
		case 6 :abstractVerification = ThuemEtAlReuse.getInstance();
				break;
		}

		if( method.equals("AbstractContract")) {
			System.out.println("Starte Proof with Abstract Contracts");
			abstractVerification.keyHandler = new AbstractContracts();
		}else if(method.equals("DefaultKeY")) {
			System.out.println("Starte Proof with DefaultKeY");
			abstractVerification.keyHandler = new DefaultKeY();
		}
		abstractVerification.warmUp(FileManager.getFirstMetaproductElement(toEvaluate), method);
		abstractVerification.performVerification(toEvaluate,evaluatePath);
		
		proofList = abstractVerification.getProofList();
		phase1ProofList = abstractVerification.getPhase1ProofList();
		proofList1And2Phase = abstractVerification.getProofListWithPhase1And2();

		updateFailedProofs();
		updateProofCount();
		updateSum();
		createXLS();
		abstractVerification.setphase1ProofList(new LinkedList<ProofHandler>());
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.featurehouse.proofautomation.evaluation.Evaluation#createXLS()
	 */
	@Override
	public void createXLS() {
		ExcelManager2.generateSingleProjectWithReuseXLS(this);
		
	}
	/**
	 * Returns the approach version according to the directory
	 * @return
	 */
	private int getApproachVersion(){
		String name = evaluatePath.getParentFile().getName();
		for(int i = 1; i<=15; i++){
			String number = String.valueOf(i);
			if(name.contains(number)){
				return i;
			}
		}
		return 0;
	}
	
	/**
	 * 
	 * @return proofList
	 */
	public List<ProofInformation> getProofList(){
		return proofList;
	}
	/**
	 * @return the phase1ProofList
	 */
	public List<ProofInformation> getPhase1ProofList() {
		return phase1ProofList;
	}

	/**
	 * @return the proofList1And2Phase
	 */
	public List<ProofInformation> getProofList1And2Phase() {
		return proofList1And2Phase;
	}
	/**
	 * removes the statistic of a give proof in the phase1ProofList and proofList
	 * @param target
	 * @param type
	 */
	public void removeProofFromSum(String target, String type){
		if(phase1ProofList != null){
			for(ProofInformation ap : phase1ProofList){
				if(ap.getTargetName().equals(target)&&ap.getTypeName().equals(type)){
					firstPhase.removeStatistics(ap.getStat());
					firstPhaseReuse.removeStatistics(ap.getReusedStat());
				}
			}
		}
		for(ProofInformation ap : proofList){
			if(ap.getTargetName().equals(target)&&ap.getTypeName().equals(type)){
				secondPhase.removeStatistics(ap.getStat());
				secondPhaseReuse.removeStatistics(ap.getReusedStat());
			}
		}
	}
	
	/**
	 * updates the list of failed proofs
	 */
	public void updateFailedProofs(){
		for(ProofInformation ap : proofList){
			if(!ap.isClosed()){
				failedProofs++;
			}
		}
	}
	
	/**
	 * Updates the Statistics 
	 */
	public void updateSum(){
		firstPhase.reset();
		firstPhaseReuse.reset();
		secondPhase.reset();
		secondPhaseReuse.reset();
		if(phase1ProofList != null){
			for(ProofInformation ap : phase1ProofList){
				firstPhase.addStatistics(ap.getStat());
				firstPhaseReuse.addStatistics(ap.getReusedStat());
			}
		}
		for(ProofInformation ap : proofList){
			secondPhase.addStatistics(ap.getStat());
			secondPhaseReuse.addStatistics(ap.getReusedStat());
		}
	}
	/**
	 * updates the number of Proofs
	 */
	public void updateProofCount(){
		proofs += proofList.size();
	}
}
