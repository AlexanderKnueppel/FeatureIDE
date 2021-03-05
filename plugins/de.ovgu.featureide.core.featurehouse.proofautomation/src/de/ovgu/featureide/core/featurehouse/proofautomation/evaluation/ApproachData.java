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
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IProject;

import de.ovgu.featureide.core.featurehouse.proofautomation.builder.BuildMap;
import de.ovgu.featureide.core.featurehouse.proofautomation.builder.MetaProductBuilderNonRigid;
import de.ovgu.featureide.core.featurehouse.proofautomation.builder.projectWorker;
import de.ovgu.featureide.core.featurehouse.proofautomation.builder.projectWorker2;
import de.ovgu.featureide.core.featurehouse.proofautomation.excel.ExcelManager2;
import de.ovgu.featureide.core.featurehouse.proofautomation.filemanagement.FileManager;
import de.ovgu.featureide.core.featurehouse.proofautomation.model.Method;
import de.ovgu.featureide.core.featurehouse.proofautomation.statistics.ProofInformation;
import de.ovgu.featureide.core.featurehouse.proofautomation.statistics.ProofStatistics;


/**
 * Registers all parameters which are needed for a approach
 * 
 * @author Marlen Herter-Bernier
 */
public class ApproachData {
	
	public ProofStatistics firstPhase = new ProofStatistics();
	public ProofStatistics secondPhase = new ProofStatistics(); 
	public ProofStatistics firstPhaseReuse = new ProofStatistics(); 
	public ProofStatistics secondPhaseReuse = new ProofStatistics();
	public int failedProofs = 0;
	public int proofs = 0;
	
	public static final String FILE_SEPERATOR = System.getProperty("file.separator");
	//Directory which should be evaluated
	public File toEvaluate;
	public File evaluatePath; //contains a subdirectory Evaluation/date time
	//File where the result of the evaluation is saved
	public File statistics;
	String method;
	String evolutionType;
	
	
	private List<SingleApproachEvaluation> projectVersions = new LinkedList<SingleApproachEvaluation>(); //contains all project versions
	/**
	 * Constructor for single execution of a verification approach
	 * @param f
	 * @param name
	 */
	public ApproachData(File f,String name,File evalPathComplete, String method, String evolutionType){
		toEvaluate = f;
		this.method = method;
		this.evolutionType =evolutionType;
		evaluatePath = evalPathComplete;
		if(name.startsWith("VA")) {
			evaluatePath = FileManager.createDir(new File (evalPathComplete.getAbsolutePath()+FILE_SEPERATOR+name));
		}
		statistics = new File (evaluatePath.getAbsolutePath()+FILE_SEPERATOR+"Evaluation Results-A"+getVersionNumber()+".xlsx");
		setProjectVersion();

	}
	
	
	/**
	 * Generates the metaproduct and if necessary the featurestub for all projects of the approach
	 */
	@SuppressWarnings("restriction")
	public void generateCode(){
		boolean newMetaproduct = true;
		int version = getVersionNumber();
		if(version == 5||version == 6){
			newMetaproduct = false;
		}

		if(method.equals("Non Rigid")) {
			LinkedList<IProject> projects = projectWorker2.getProjectsByApproach(toEvaluate.getName());
			projectWorker2.generateAllMetaproductsForApproach(projects, newMetaproduct);
			projectWorker2.generateAllFeatureStubsForApproach(projects);

			for(IProject project : projects) {
				MetaProductBuilderNonRigid.prepareMetaproductForNonRigid(new File(toEvaluate.getAbsolutePath()+FILE_SEPERATOR+project.getName()+FILE_SEPERATOR+FileManager.metaproductDir));
				BuildMap.parseMethodsFromFeatureModel(project, projectVersions);
			}
		}else {
			LinkedList<IProject> projects = projectWorker.getProjectsByApproach(toEvaluate.getName());
			projectWorker.generateAllMetaproductsForApproach(projects, newMetaproduct);
			if(getVersionNumber()==1){
				projectWorker.generateAllFeatureStubsForApproach(projects);
			}
		}

	}
	
	/**
	 * Adds all subdirectories to the list, if they contain a project Version
	 */
	private void setProjectVersion(){
		File[] allFiles = toEvaluate.listFiles();
		for(File f: allFiles){
			if(f.isDirectory() && isVersion(f)){
				projectVersions.add(new SingleApproachEvaluation(f,getVersionNumber(),evaluatePath.getAbsolutePath()+FILE_SEPERATOR+f.getName(),method,evolutionType));
			}
		}
	}
	/**
	 * Gets a list of all Projects saved
	 * @return
	 */
	public List<SingleApproachEvaluation> getProjectVersion(){
		return projectVersions;
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
		if(getVersionNumber()==3||getVersionNumber()==4||getVersionNumber()==5||getVersionNumber()==6){
			ExcelManager2.generateSingleApproachEvaluationWithReuseXLS(this);
		}
		else{
			ExcelManager2.generateSingleApproachTwoPhaseEvaluationWithReuseXLS(this);
		}
	}
	
	/**
	 * Adds the sums of the sub evaluation ev to the current evaluation
	 * @param s
	 */
	public void updateStatistics(SingleApproachEvaluation s){
		this.firstPhase.addStatistics(s.firstPhase);
		this.secondPhase.addStatistics(s.secondPhase);
		this.firstPhaseReuse.addStatistics(s.firstPhaseReuse);
		this.secondPhaseReuse.addStatistics(s.secondPhaseReuse);
	}
	
	/**
	 * 
	 * @param singleApproachEvaluation
	 */
	public void addFailedProofs(SingleApproachEvaluation singleApproachEvaluation){
		this.failedProofs += singleApproachEvaluation.failedProofs;
	}
	/**
	 * 
	 * @param singleApproachEvaluation
	 */
	public void addProofsCount(SingleApproachEvaluation singleApproachEvaluation){
		this.proofs += singleApproachEvaluation.proofs;
	}
	
	/**
	 * 	gets all Disjoints proofs
	 * @return
	 */
	public List<ProofStats> getAllDisjointProofs(){
		List<ProofStats> evaluationProofs = new LinkedList<ProofStats>();
		for(SingleApproachEvaluation s: projectVersions){
			List<ProofInformation> firstPhaseProofs = s.getPhase1ProofList();
			List<ProofInformation> allProofs = s.getProofList();
			if(firstPhaseProofs!=null){
				for(ProofInformation proofInformation: firstPhaseProofs){
					ProofStats proofStats = getListElement(proofInformation.getTargetName(),proofInformation.getTypeName(),evaluationProofs);
					if(proofStats == null){
						proofStats = new ProofStats(proofInformation.getTargetName(),proofInformation.getTypeName());
						evaluationProofs.add(proofStats);
					}
					proofStats.addSum(proofInformation.getStat(),proofInformation.getReusedStat());
				}
			}
			for(ProofInformation proofInformation: allProofs){
				ProofStats proofStats = getListElement(proofInformation.getTargetName(),proofInformation.getTypeName(),evaluationProofs);
				if(proofStats == null){
					proofStats = new ProofStats(proofInformation.getTargetName(),proofInformation.getTypeName());
					evaluationProofs.add(proofStats);
				}
				proofStats.addSum(proofInformation.getStat(),proofInformation.getReusedStat());
				if(!proofInformation.isClosed()){
					proofStats.setClosed(false);
				}
			}
		}
		return evaluationProofs;
	}
	
	/**
	 * gets a given Element of the Proofstats List
	 * @param target
	 * @param type
	 * @param proofStatsList
	 * @return
	 */	
	public ProofStats getListElement(String target, String type,List<ProofStats> proofStatsList) {
		for(ProofStats ps: proofStatsList ) {
			if(ps.getTarget().equals(target)&& ps.getType().equals(type)){
				return ps;
			}
		}
		return null;
	}
	/**
	 * removes a failed proof from all the Statisticslists. So the failed proofs won't be counted.
	 * @param ep
	 */
	public void removeFailedProofs(List<ProofStats> ep){
		for(SingleApproachEvaluation s: projectVersions){
			for(ProofStats e: ep){
				s.removeProofFromSum(e.getTarget(), e.getType());
			}
			this.updateStatistics(s);
		}
	}
}
