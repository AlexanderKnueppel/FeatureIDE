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

import de.ovgu.featureide.core.featurehouse.proofautomation.excel.ExcelManager;
import de.ovgu.featureide.core.featurehouse.proofautomation.key.AutomatingProject;
import de.ovgu.featureide.core.featurehouse.proofautomation.key.AutomatingProof;

/**
 * This class represents a single Evaluation phase 
 * (Phase 1 Fefalution, Phase 2 Metaproduct, Phase 3 Concrete Contracts, Phase 4 Method Inlining, Phase 5 Thuem et al.)
 * 
 * @author Stefanie
 */
public class EvaluationPhase extends Evaluation{
	private List<SingleProject> bankAccountVersions = new LinkedList<SingleProject>(); //contains all BankAccount versions
	
	/**
	 * Constructor
	 * gets a directory of a single phase and sets the statistics file and the BankAccount list
	 * @param f
	 */
	public EvaluationPhase(File f){
		this.toEvaluate = f;
		statistics = new File (toEvaluate.getAbsolutePath()+FILE_SEPERATOR+"Evaluation Results-A"+getVersionNumber()+".xlsx");
		setBankAccountVersion();
	}
	
	/**
	 * Returns the phase number of the evaluation phase
	 * @return int [1,5]
	 */
	public int getVersionNumber(){
		String name = toEvaluate.getName();
		if(name.contains("1")){
			return 1;
		}
		else if(name.contains("2")){
			return 2;
		}
		else if(name.contains("3")){
			return 3;
		}
		else if(name.contains("4")){
			return 4;
		}
		else if(name.contains("5")){
			return 5;
		}
		return 0;
	}
	
	public List<SingleProject> getBankAccountVersion(){
		return bankAccountVersions;
	}

	/**
	 * Adds all subdirectories to the BankAccount list, if they contain a BankAccountVersion
	 */
	private void setBankAccountVersion(){
		File[] allFiles = toEvaluate.listFiles();
		for(File f: allFiles){
			if(f.isDirectory() && isVersion(f)){
				bankAccountVersions.add(new SingleProject(f,toEvaluate.getName()));
			}
		}
	}
	
	/**
	 * Returns true, if the given File is a BankAccount version
	 * @param f
	 * @return
	 */
	private boolean isVersion(File f){
		if(f.getName().contains("BankAccount")){
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
		ExcelManager.generateSinglePhaseEvaluationXLS(this);
	}
	
	/**
	 * Performs the Evaluation of one Phase
	 */
	public void performEvaluation(){
		for(SingleProject s : bankAccountVersions){
			s.performEvaluation();
			this.updateStatistics(s);
		}
		createXLS();
	}
	
}
