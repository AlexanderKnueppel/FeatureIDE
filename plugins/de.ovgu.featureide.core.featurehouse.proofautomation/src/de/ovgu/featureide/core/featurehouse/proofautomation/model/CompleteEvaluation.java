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

import de.ovgu.featureide.core.featurehouse.proofautomation.excel.ExcelManager;
import de.ovgu.featureide.core.featurehouse.proofautomation.filemanagement.FileManager;

/**
 * Represents a complete Evaluation 
 * 
 * @author Stefanie
 */
public class CompleteEvaluation extends Evaluation{
	
	List<EvaluationApproach> allApproaches = new LinkedList<EvaluationApproach>(); //contains all single Evaluation approaches
	
	public List<EvaluationApproach> getAllApproaches(){
		return allApproaches;
	}
	
	/**
	 * Constructor 
	 * gets a directory which contains all evaluation approaches and sets the statistics file and the Evaluation Approach list
	 * @param toEvaluate
	 */
	public CompleteEvaluation(File f){
		super(f);
		date = new Date();
		File evalDir = FileManager.createDir(new File(toEvaluate.getAbsolutePath()+FILE_SEPERATOR+FileManager.evaluationDir));
		evaluatePath = FileManager.createDateDir(date, evalDir);
		statistics = new File (evaluatePath.getAbsolutePath()+FILE_SEPERATOR+"Evaluation Results.xlsx");
		setEvaluationApproach();
	}

	/**
	 * Adds all subdirectories which contains a evaluation Approach to the list 
	 */
	//todo:replace with static list of approaches
	private void setEvaluationApproach(){
/*		File[] allFiles = toEvaluate.listFiles();
		for(File f: allFiles){
			if(f.isDirectory() && isEvaluationApproach(f) &&!f.getName().equals(FileManager.evaluationDir)){
				allApproaches.add(new EvaluationApproach(f,date,false));
			}
		}*/
		allApproaches.add(new EvaluationApproach(this.toEvaluate,date,false,"VA1 (EVEFI)",this.evaluatePath));
		allApproaches.add(new EvaluationApproach(this.toEvaluate,date,false,"VA2 (Metaproduct)",this.evaluatePath));
		allApproaches.add(new EvaluationApproach(this.toEvaluate,date,false,"VA3 (Concrete)",this.evaluatePath));
		allApproaches.add(new EvaluationApproach(this.toEvaluate,date,false,"VA4 (MI)",this.evaluatePath));
		allApproaches.add(new EvaluationApproach(this.toEvaluate,date,false,"VA5 (Thuem et al.)",this.evaluatePath));
		allApproaches.add(new EvaluationApproach(this.toEvaluate,date,false,"VA6",this.evaluatePath));
		allApproaches.add(new EvaluationApproach(this.toEvaluate,date,false,"VA9",this.evaluatePath));
	}
	
	/**
	 * Returns true if the given file is a evaluation Approach
	 * @param f
	 * @return
	 */
	//todo: remove
	
	/**
	 * Creates an XLSX File with the result of the evaluation
	 */
	public void createXLS(){
		ExcelManager.generateAllApproachEvaluationWithReuseXLS(this);;
	}
	
	/**
	 * Performs the complete Evaluation
	 */
	public void performEvaluation(){
		for(EvaluationApproach e: allApproaches){
			e.performEvaluation();
			this.addFailedProofs(e);
			this.addProofsCount(e);
		}
		List<EvaluationProof> failedProofs = getListOfAllFailedProofs();
		for(EvaluationApproach e: allApproaches){
			e.removeFailedProofs(failedProofs);
			e.createXLS();
			this.updateStatistics(e);
		}
		createXLS();
	}
	
	public List<EvaluationProof> getListOfAllFailedProofs(){
		List<EvaluationProof> failed = new LinkedList<EvaluationProof>();
		for(EvaluationApproach ea: allApproaches){
			for(EvaluationProof ep :ea.getAllDisjointProofs()){
				if(!ep.isClosed()){
					if(!isInList(failed,ep.getTarget(),ep.getType())){
						failed.add(ep);
					}
				}
			}
		}
		return failed;
	}
	
	private boolean isInList(List<EvaluationProof> e, String target, String type){
		for(EvaluationProof ep: e){
			if(ep.getTarget().equals(target)&&ep.getType().equals(type)){
				return true;
			}
		}
		return false;
	}
}
