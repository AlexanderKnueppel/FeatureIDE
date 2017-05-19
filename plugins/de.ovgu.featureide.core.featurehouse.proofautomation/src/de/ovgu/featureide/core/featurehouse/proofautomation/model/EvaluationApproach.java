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

import org.eclipse.core.resources.IProject;

import de.ovgu.featureide.core.featurehouse.proofautomation.builder.projectWorker;
import de.ovgu.featureide.core.featurehouse.proofautomation.excel.ExcelManager;
import de.ovgu.featureide.core.featurehouse.proofautomation.filemanagement.FileManager;
import de.ovgu.featureide.core.featurehouse.proofautomation.key.AutomatingProof;
import de.ovgu.featureide.core.featurehouse.proofautomation.key.startNewJVM;

/**
 * This class represents a single Evaluation approach 
 * (Approach 1 Fefalution, Approach 2 Metaproduct, Approach 3 Concrete Contracts, Approach 4 Method Inlining, Approach 5 Thuem et al.)
 * 
 * @author Stefanie
 */
@SuppressWarnings("restriction")
public class EvaluationApproach extends Evaluation{
	public boolean singleExecution = true;
	private List<SingleProject> projectVersions = new LinkedList<SingleProject>(); //contains all project versions
	
	/**
	 * Constructor
	 * gets a directory of a single approach and sets the statistics file and the BankAccount list
	 * @param f
	 */
	public EvaluationApproach(File f, Date d,boolean singleExecution){
		super(f);
		date = d;
		if(d== null){
			date = new Date();
		}
		File evalDir = FileManager.createDir(new File(toEvaluate.getAbsolutePath()+FILE_SEPERATOR+FileManager.evaluationDir));
		evaluatePath = FileManager.createDateDir(date, evalDir);
		statistics = new File (evaluatePath.getAbsolutePath()+FILE_SEPERATOR+"Evaluation Results-A"+getVersionNumber()+".xlsx");
		setProjectVersion();
		generateCode();
		this.singleExecution = singleExecution;
	}
	
	/**
	 * Generates the metaproduct and if necessary the featurestub for all projects of the approach
	 */
	private void generateCode(){
		LinkedList<IProject> projects = projectWorker.getProjectsByApproach(toEvaluate.getName());
		boolean newMetaproduct = true;
		int version = getVersionNumber();
		if(version == 5||version == 6||version == 7||version == 8){
			newMetaproduct = false;
		}
		projectWorker.generateAllMetaproductsForApproach(projects, newMetaproduct);
		if(getVersionNumber()==1){
			projectWorker.generateAllFeatureStubsForApproach(projects);
		}
	}
	/**
	 * Returns the Approach number of the evaluation Approach
	 * @return int [1,15]
	 */
	public int getVersionNumber(){
		String name = toEvaluate.getName();
		for(int i = 1; i<=15; i++){
			String number = String.valueOf(i);
			if(name.contains(number)){
				return i;
			}
		}
		return 0;
	}
	
	public List<SingleProject> getProjectVersion(){
		return projectVersions;
	}

	/**
	 * Adds all subdirectories to the BankAccount list, if they contain a project Version
	 */
	private void setProjectVersion(){
		File[] allFiles = toEvaluate.listFiles();
		for(File f: allFiles){
			if(f.isDirectory() && isVersion(f)){
				projectVersions.add(new SingleProject(f,date,getVersionNumber()));
			}
		}
	}
	
	/**
	 * Returns true, if the given File is a project version
	 * @param f
	 * @return
	 */
	private boolean isVersion(File f){
		if(f.getName().contains(FileManager.projectName)){
			return true;
		}
		else{
			return false;
		}
	}
	
	/**
	 * Creates an XLSX File with the result of the evaluation
	 */
	public void createXLS(){
		if(getVersionNumber()==3||getVersionNumber()==4||getVersionNumber()==5||getVersionNumber()==9){
			ExcelManager.generateSingleApproachEvaluationWithReuseXLS(this);
		}
		else{
			ExcelManager.generateSingleApproachTwoPhaseEvaluationWithReuseXLS(this);
		}
	}
	
	/**
	 * Performs the Evaluation of one Approach
	 */
	public void performEvaluation(){
		for(SingleProject s : projectVersions){
			startNewJVM.startNewProcess(s.toEvaluate, s.evaluatePath);
		}
		for(SingleProject s: projectVersions){
			ExcelManager.updateSingleProjectsWithReuse(s);
			if(this.singleExecution){
				this.updateStatistics(s);
			}
			this.addFailedProofs(s);
			this.addProofsCount(s);
		}
		if(this.singleExecution){
			createXLS();
		}
	}
	
	public List<EvaluationProof> getAllDisjointProofs(){
		List<EvaluationProof> evaluationProofs = new LinkedList<EvaluationProof>();
		for(SingleProject s: projectVersions){
			List<AutomatingProof> first = s.getPhase1ProofList();
			List<AutomatingProof> second = s.getProofList();
			if(first!=null){
				for(AutomatingProof a: first){
					EvaluationProof ep = getListElement(a.getTargetName(),a.getTypeName(),evaluationProofs);
					if(ep == null){
						ep = new EvaluationProof(a.getTargetName(),a.getTypeName());
						evaluationProofs.add(ep);
					}
					ep.addSum(a.getStat(),a.getReusedStat());
				}
			}
			for(AutomatingProof a: second){
				EvaluationProof ep = getListElement(a.getTargetName(),a.getTypeName(),evaluationProofs);
				if(ep == null){
					ep = new EvaluationProof(a.getTargetName(),a.getTypeName());
					evaluationProofs.add(ep);
				}
				ep.addSum(a.getStat(),a.getReusedStat());
				if(!a.isClosed()){
					ep.setClosed(false);
				}
			}
		}
		return evaluationProofs;
	}
	
	public EvaluationProof getListElement(String target, String type,List<EvaluationProof> ep){
		for(EvaluationProof e: ep){
			if(e.getTarget().equals(target)&&e.getType().equals(type)){
				return e;
			}
		}
		return null;
	}
	
	public void removeFailedProofs(List<EvaluationProof> ep){
		for(SingleProject s: projectVersions){
			for(EvaluationProof e: ep){
				s.removeProofFromSum(e.getTarget(), e.getType());
			}
			this.updateStatistics(s);
		}
	}
}
