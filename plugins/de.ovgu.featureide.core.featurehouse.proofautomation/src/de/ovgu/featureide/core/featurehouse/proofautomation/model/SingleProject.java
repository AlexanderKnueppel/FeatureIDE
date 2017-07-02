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

import java.io.File;
import java.util.Date;
import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.core.featurehouse.proofautomation.builder.projectWorker;
import de.ovgu.featureide.core.featurehouse.proofautomation.configuration.Configuration;
import de.ovgu.featureide.core.featurehouse.proofautomation.excel.ExcelManager;
import de.ovgu.featureide.core.featurehouse.proofautomation.filemanagement.FileManager;
import de.ovgu.featureide.core.featurehouse.proofautomation.key.AutomatingProject;
import de.ovgu.featureide.core.featurehouse.proofautomation.key.AutomatingProof;
/**
 * This class represents a single project 
 * 
 * @author Stefanie
 */
public class SingleProject extends Evaluation{
	private List<AutomatingProof> phase1ProofList = new LinkedList<AutomatingProof>();
	private List<AutomatingProof> proofList = new LinkedList<AutomatingProof>(); //contains all Automating proofs of this project
	private List<AutomatingProof> proofList1And2Phase = new LinkedList<AutomatingProof>();
	private static final String FILE_SEPERATOR = System.getProperty("file.separator");
	private int evalVersion;

	/**
	 * Constructor for execution in an verification approach
	 * Uses a given evaluatePath instead of a new
	 * @param f
	 * @param evalVersion
	 * @param evaluatePath
	 */
	public SingleProject(File f, int evalVersion, String evaluatePath){
		super(f);
		this.evaluatePath = FileManager.createDir(new File(evaluatePath));
		if(evalVersion>0){
			this.evalVersion = evalVersion;
		}
		else{
			this.evalVersion = getApproachVersion();
		}
		this.statistics = new File (evaluatePath+FILE_SEPERATOR+"Evaluation Results.xlsx");
	}
	
	public List<AutomatingProof> getProofList(){
		return proofList;
	}
	
	/**
	 * Constructor for proofing a single project version
	 * @param f
	 * @param verificationApproachName
	 */
	public SingleProject(File f, String verificationApproachName){
		super(f);
		date = new Date();
		File dateDir = FileManager.createDateDir(date, new File(f.getParent()+FILE_SEPERATOR+FileManager.evaluationDir));
		File vaDir = FileManager.createDir(new File(dateDir+FILE_SEPERATOR+verificationApproachName));
		this.evaluatePath = FileManager.createDir(new File(vaDir+FILE_SEPERATOR+f.getName()));
		this.evalVersion = getApproachVersion();
		this.statistics = new File (evaluatePath+FILE_SEPERATOR+"Evaluation Results.xlsx");
		boolean newMetaproduct=true,featurestub=false;
		if(evalVersion == 5||evalVersion == 6){
			newMetaproduct = false;
		}
		if(evalVersion==1){
			featurestub=true;
		}
		projectWorker.generateCodeForSingleProject(f.getName(), featurestub, newMetaproduct);
	}
	
	/**
	 * @return the phase1ProofList
	 */
	public List<AutomatingProof> getPhase1ProofList() {
		return phase1ProofList;
	}

	/**
	 * @return the proofList1And2Phase
	 */
	public List<AutomatingProof> getProofList1And2Phase() {
		return proofList1And2Phase;
	}

	/**
	 * Returns the apporach version according to the directory
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
	 * Performs the evaluation of a single approach dependent on the current approach
	 */
	public void performEvaluation(){
		if(evalVersion == 5||evalVersion == 6){
			Configuration.setCurrentMetaproductwithDispatcher(false);
		}
		else{
			Configuration.setCurrentMetaproductwithDispatcher(true);
		}
		FileManager.initFolders(evaluatePath, evalVersion);
		AutomatingProject aproj = AutomatingProject.getInstance();
		aproj.warmUp(FileManager.getFirstMetaproductElement(toEvaluate));
		switch(evalVersion){
			case 1 :aproj.performVa1(toEvaluate,evaluatePath);
					break;
			case 2 :aproj.performVa2(toEvaluate,evaluatePath);
					break;
			case 3 :aproj.performVa3(toEvaluate,evaluatePath);
					break;
			case 4 :aproj.performVa4(toEvaluate,evaluatePath);
					break;
			case 5 :aproj.performVa5(toEvaluate,evaluatePath);
					break;
			case 6 :aproj.performVa6(toEvaluate,evaluatePath);
					break;
		}
		proofList = aproj.getProofList();
		phase1ProofList = aproj.getPhase1ProofList();
		proofList1And2Phase = aproj.getProofListWithPhase1And2();
		updateFailedProofs();
		updateProofCount();
		updateSum();
		createXLS();
		aproj.setPhase1ProofList(new LinkedList<AutomatingProof>());
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
			for(AutomatingProof ap : phase1ProofList){
				firstPhase.addStatistics(ap.getStat());
				firstPhaseReuse.addStatistics(ap.getReusedStat());
			}
		}
		for(AutomatingProof ap : proofList){
			secondPhase.addStatistics(ap.getStat());
			secondPhaseReuse.addStatistics(ap.getReusedStat());
		}
	}
	
	public void removeProofFromSum(String target, String type){
		if(phase1ProofList != null){
			for(AutomatingProof ap : phase1ProofList){
				if(ap.getTargetName().equals(target)&&ap.getTypeName().equals(type)){
					firstPhase.removeStatistics(ap.getStat());
					firstPhaseReuse.removeStatistics(ap.getReusedStat());
				}
			}
		}
		for(AutomatingProof ap : proofList){
			if(ap.getTargetName().equals(target)&&ap.getTypeName().equals(type)){
				secondPhase.removeStatistics(ap.getStat());
				secondPhaseReuse.removeStatistics(ap.getReusedStat());
			}
		}
	}
	
	public void updateFailedProofs(){
		for(AutomatingProof ap : proofList){
			if(!ap.isClosed()){
				failedProofs++;
			}
		}
	}
	
	public void updateProofCount(){
		proofs += proofList.size();
	}
	
	/**
	 * Creates an XLSX File with the result of the evaluation
	 */
	public void createXLS(){
		ExcelManager.generateSingleProjectWithReuseXLS(this);
	}
	
}
