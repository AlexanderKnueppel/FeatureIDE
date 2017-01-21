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
public class EvaluationPhase extends Evaluation{
	private List<SingleProject> bankAccountVersions = new LinkedList<SingleProject>();
	
	public EvaluationPhase(File f){
		this.toEvaluate = f;
		statistics = new File (toEvaluate.getAbsolutePath()+FILE_SEPERATOR+"Evaluation Results-.xls");
		setBankAccountVersion();
	}
	
	public List<SingleProject> getBankAccountVersion(){
		return bankAccountVersions;
	}

	private void setBankAccountVersion(){
		File[] allFiles = toEvaluate.listFiles();
		for(File f: allFiles){
			if(f.isDirectory() && isVersion(f)){
				bankAccountVersions.add(new SingleProject(f));
			}
		}
	}
	
	private boolean isVersion(File f){
		if(f.getName().contains("BankAccount")){
			return true;
		}
		else{
			return false;
		}
	}
	
	public void createXLS(){
		ExcelManager.generateSinglePhaseEvaluationXLS(this);
	}
	
	public void performEvaluation(){
		System.out.println("This should perform a single Evaluation Phase!");
	}
	
}
