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
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IProject;

import de.ovgu.featureide.core.featurehouse.proofautomation.builder.BuilderUtil;
import de.ovgu.featureide.core.featurehouse.proofautomation.builder.FeatureStubBuilder;
import de.ovgu.featureide.core.featurehouse.proofautomation.builder.MetaProductBuilder;
import de.ovgu.featureide.core.featurehouse.proofautomation.builder.projectWorker;
import de.ovgu.featureide.core.featurehouse.proofautomation.excel.ExcelManager;
import de.ovgu.featureide.core.featurehouse.proofautomation.filemanagement.FileManager;
import de.ovgu.featureide.core.featurehouse.proofautomation.key.AutomatingProject;
import de.ovgu.featureide.core.featurehouse.proofautomation.key.AutomatingProof;
import de.ovgu.featureide.core.featurehouse.proofautomation.key.startNewJVM;

/**
 * This class represents a single Evaluation approach 
 * (Approach 1 Fefalution, Approach 2 Metaproduct, Approach 3 Concrete Contracts, Approach 4 Method Inlining, Approach 5 Thuem et al.)
 * 
 * @author Stefanie
 */
public class EvaluationApproach extends Evaluation{
	private List<SingleProject> projectVersions = new LinkedList<SingleProject>(); //contains all project versions
	
	/**
	 * Constructor
	 * gets a directory of a single approach and sets the statistics file and the BankAccount list
	 * @param f
	 */
	public EvaluationApproach(File f){
		super(f);
		statistics = new File (evaluatePath.getAbsolutePath()+FILE_SEPERATOR+"Evaluation Results-A"+getVersionNumber()+".xlsx");
		setProjectVersion();
//		generateCode();
	}
	
	private void generateCode(){
		LinkedList<IProject> projects = projectWorker.getProjectsByApproach(toEvaluate.getName());
/*		boolean newMetaproduct = true;
		if(getVersionNumber() == 5){
			newMetaproduct = false;
		}
		MetaProductBuilder.generateAllMetaproductsForApproach(projects, newMetaproduct);*/
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
				projectVersions.add(new SingleProject(f,getVersionNumber()));
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
		ExcelManager.generateSingleApproachEvaluationXLS(this);
	}
	
	/**
	 * Performs the Evaluation of one Approach
	 */
	public void performEvaluation(){
		for(SingleProject s : projectVersions){
			startNewJVM.startNewProcess(s.toEvaluate, s.evaluatePath);
		}
		for(SingleProject s: projectVersions){
			ExcelManager.updateSingleProjects(s);
			this.updateStatistics(s);
		}
		createXLS();
	}
	
}
