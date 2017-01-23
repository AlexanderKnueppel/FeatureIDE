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

/**
 * Represents a complete Evaluation 
 * 
 * @author Stefanie
 */
public class CompleteEvaluation extends Evaluation{
	
	List<EvaluationPhase> allPhases = new LinkedList<EvaluationPhase>(); //contains all single Evaluation phases
	
	public List<EvaluationPhase> getAllPhases(){
		return allPhases;
	}
	
	/**
	 * Constructor 
	 * gets a directory which contains all evaluation phases and sets the statistics file and the Evaluation phase list
	 * @param toEvaluate
	 */
	public CompleteEvaluation(File toEvaluate){
		this.toEvaluate = toEvaluate;
		statistics = new File (toEvaluate.getAbsolutePath()+FILE_SEPERATOR+"Evaluation Results.xlsx");
		setEvaluationPhases();
	}

	/**
	 * Adds all subdirectories which contains a evaluation phase to the list 
	 */
	private void setEvaluationPhases(){
		File[] allFiles = toEvaluate.listFiles();
		for(File f: allFiles){
			if(f.isDirectory() && isEvaluationPhase(f)){
				allPhases.add(new EvaluationPhase(f));
			}
		}
	}
	
	/**
	 * Returns true if the given file is a evaluation phase
	 * @param f
	 * @return
	 */
	private boolean isEvaluationPhase(File f){
		File[] content = f.listFiles();
		for(File c: content){
			if(c.getName().contains("BankAccount")){
				return true;
			}
		}
		return false;
	}
	
	/**
	 * Creates an XLSX File with the result of the evaluation
	 */
	public void createXLS(){
		ExcelManager.generateAllPhasesEvaluationXLS(this);;
	}
	
	/**
	 * Performs the complete Evaluation
	 */
	public void performEvaluation(){
		for(EvaluationPhase e: allPhases){
			e.performEvaluation();
			this.updateStatistics(e);
		}
		createXLS();
	}
}
