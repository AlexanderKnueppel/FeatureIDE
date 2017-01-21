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
 * TODO description
 * 
 * @author Stefanie
 */
public class CompleteEvaluation extends Evaluation{
	List<EvaluationPhase> allPhases = new LinkedList<EvaluationPhase>();
	
	public List<EvaluationPhase> getAllPhases(){
		return allPhases;
	}
	
	public CompleteEvaluation(File toEvaluate){
		this.toEvaluate = toEvaluate;
		statistics = new File (toEvaluate.getAbsolutePath()+FILE_SEPERATOR+"Evaluation Results.xls");
		setEvaluationPhases();
	}

	private void setEvaluationPhases(){
		File[] allFiles = toEvaluate.listFiles();
		for(File f: allFiles){
			if(f.isDirectory() && isEvaluationPhase(f)){
				allPhases.add(new EvaluationPhase(f));
			}
		}
	}
	
	private boolean isEvaluationPhase(File f){
		File[] content = f.listFiles();
		for(File c: content){
			if(c.getName().contains("BankAccount")){
				return true;
			}
		}
		return false;
	}
	
	public void createXLS(){
		ExcelManager.generateAllPhasesEvaluationXLS(this);;
	}
	
	public void performEvaluation(){
		System.out.println("This should perform the complete Evaluation!");
	}
}
