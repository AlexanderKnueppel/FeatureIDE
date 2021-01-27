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
import java.util.Date;
import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.core.featurehouse.proofautomation.builder.MetaProductBuilderNonRigid;
import de.ovgu.featureide.core.featurehouse.proofautomation.excel.ExcelManager2;
import de.ovgu.featureide.core.featurehouse.proofautomation.filemanagement.FileManager;
import de.ovgu.featureide.core.featurehouse.proofautomation.key.startNewJVM;


/**
 * Represents a Evaluation over all approaches 
 * 
 * @author Stefanie
 */
public class CompleteApproachesEvaluation extends Evaluation{
	public int failedProofs = 0;
	public int proofs = 0;
	List<ApproachData> allProjects = new LinkedList<ApproachData>(); //contains all single Evaluation approaches
	
	public List<ApproachData> getAllApproaches(){
		return allProjects;
	}
	private ApproachData approachData;

	/**
	 * Constructor 
	 * gets a directory which contains one evaluation approache and sets the statistics file and the Evaluation Approach list
	 * @param toEvaluate
	 */
	public CompleteApproachesEvaluation(File f, String verificationType, String method) {
		super(f);
		this.verificationType = verificationType;
		this.method = method;
		date = new Date();
		if(verificationType.startsWith("0")) {
			File evalDir = FileManager.createDir(new File(toEvaluate.getAbsolutePath()+FILE_SEPERATOR+FileManager.evaluationDir));
			evaluatePath = FileManager.createDateDir(date, evalDir);
			statistics = new File (evaluatePath.getAbsolutePath()+FILE_SEPERATOR+"Evaluation Results.xlsx");
			setAllEvaluationApproaches();
		}else {
			File dateDir = FileManager.createDateDir(date, new File(f.getAbsolutePath()+FILE_SEPERATOR+FileManager.evaluationDir));
			evaluatePath = FileManager.createDir(new File (dateDir.getAbsolutePath()+FILE_SEPERATOR+verificationType));
			statistics = new File (evaluatePath.getAbsolutePath()+FILE_SEPERATOR+"Evaluation Results-A"+getVersionNumber()+".xlsx");
			setOneEvaluationApproach();	
		}	
	}
	/**
	 * Adds all subdirectories which contains a evaluation Approach to the list 
	 */
	private void setAllEvaluationApproaches(){
		allProjects.add(new ApproachData(this.toEvaluate,"VA1 (EVEFI)",this.evaluatePath,method));
		allProjects.add(new ApproachData(this.toEvaluate,"VA2 (Metaproduct)",this.evaluatePath,method));
		allProjects.add(new ApproachData(this.toEvaluate,"VA3 (Concrete)",this.evaluatePath,method));
		allProjects.add(new ApproachData(this.toEvaluate,"VA4 (Method Inlining)",this.evaluatePath,method));
		allProjects.add(new ApproachData(this.toEvaluate,"VA5 (Thuem et al.)",this.evaluatePath,method));
		allProjects.add(new ApproachData(this.toEvaluate,"VA6 (Thuem et al. with Reuse)",this.evaluatePath,method));
		
	}
	
	/**
	 * Adds one subdirectorie which contains a evaluation Approach to the list 
	 */
	private void setOneEvaluationApproach(){
		allProjects.add(new ApproachData(this.toEvaluate,verificationType,this.evaluatePath,method));
	}
	
	/**
	 * Creates an XLSX File with the result of the evaluation
	 */
	public void createXLS(){
		if(allProjects.size() == 1) {
			int versionNr = getVersionNumber();
			if(versionNr==3||versionNr==4||versionNr==5||versionNr==6){
				ExcelManager2.generateSingleApproachEvaluationWithReuseXLS(approachData);
			}else{
				ExcelManager2.generateSingleApproachTwoPhaseEvaluationWithReuseXLS(approachData);
			}
		}else {
			ExcelManager2.generateAllApproachEvaluationWithReuseXLS(this);
			ExcelManager2.generateAllApproachWithInitSeperated(this);
		}
	}
	
	/**
	 * Returns the Approach number of the evaluation Approach
	 * @return int [1,15]
	 */
	public int getVersionNumber(){
		String name = evaluatePath.getName();
		for(int i = 1; i<=15; i++){
			String number = String.valueOf(i);
			if(name.contains(number)){
				return i;
			}
		}
		return 0;
	}
	
	/**
	 * Performs the complete Evaluation
	 */
	public void performEvaluation(){
		for(ApproachData approachData: allProjects){			
			approachData.generateCode();

	/*		for(SingleApproachEvaluation s : approachData.getProjectVersion()){
				MetaProductBuilderNonRigid.prepareMetaproductForNonRigid(new File(s.toEvaluate.getAbsolutePath()+FILE_SEPERATOR+FileManager.metaproductDir));

				startNewJVM.startNewProcess(s.toEvaluate, s.evaluatePath,method);
			}
		
			for(SingleApproachEvaluation s : approachData.getProjectVersion()){
				ExcelManager2.updateSingleProjectsWithReuse(s);
				approachData.addFailedProofs(s);
				approachData.addProofsCount(s);
				if(allProjects.size() == 1) {
					this.updateStatistics(approachData);
				}else {
					this.addFailedProofs(approachData);
					this.addProofsCount(approachData);	
				}
			}
			

			this.approachData = approachData;
		}
		
		if(allProjects.size() == 1) {
			createXLS();
		}else {
			List<ProofStats> failedProofs = getListOfAllFailedProofs();
			for(ApproachData e: allProjects){
				e.removeFailedProofs(failedProofs);
				e.createXLS();
				updateStatistics(e);
			}
			createXLS();
			*/
		}

	}
	
	/**
	 * 
	 * @return List<ProofStats> failed
	 */
	public List<ProofStats> getListOfAllFailedProofs(){
		List<ProofStats> failed = new LinkedList<ProofStats>();
		for(ApproachData e: allProjects){
			for(ProofStats ep :e.getAllDisjointProofs()){
				if(!ep.isClosed()){
					if(!isInList(failed,ep.getTarget(),ep.getType())){
						failed.add(ep);
					}
				}
			}
		}
		return failed;
	}
	
	/**
	 * 
	 * @param e
	 * @param target
	 * @param type
	 * @return boolean
	 */
	private boolean isInList(List<ProofStats> e, String target, String type){
		for(ProofStats ep: e){
			if(ep.getTarget().equals(target)&&ep.getType().equals(type)){
				return true;
			}
		}
		return false;
	}
	
	/**
	 * 
	 * @param e
	 */
	public void addFailedProofs(ApproachData e){
		this.failedProofs += e.failedProofs;
	}
	
	/**
	 * 
	 * @param e
	 */
	public void addProofsCount(ApproachData e){
		this.proofs += e.proofs;
	}
}
