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
import java.util.Set;

import de.ovgu.featureide.core.featurehouse.proofautomation.builder.MetaProductBuilder;
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
	private List<AutomatingProof> proofList = new LinkedList<AutomatingProof>(); //contains all Automating proofs of this project
	private static final String FILE_SEPERATOR = System.getProperty("file.separator");
	private int evalVersion;
	
	/**
	 * Constructor
	 * gets a directory of a project version and the current evaluation approach
	 * and sets the statistic file
	 * @param f
	 */
	public SingleProject(File f, int evalVersion){
		super(f);
		this.evalVersion = evalVersion;
		this.statistics = new File (evaluatePath.getAbsolutePath()+FILE_SEPERATOR+"Evaluation Results.xlsx");
	}
	
	public List<AutomatingProof> getProofList(){
		return proofList;
	}
	
	/**
	 * Performs the evaluation of a single approach dependent on the current approach
	 */
	public void performEvaluation(){
		FileManager.initFolders(evaluatePath, evalVersion);
		MetaProductBuilder.prepareMetaProduct(new File(toEvaluate.getAbsolutePath()+FILE_SEPERATOR+FileManager.metaproductDir));
		AutomatingProject aproj = AutomatingProject.getInstance();
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
		}
		proofList = aproj.getProofList();
		updateSum();
		createXLS();
		aproj.relaseMemoryOfProject();
		aproj = null;
		proofList = null;
		System.gc();
		System.out.println();
	}
	
	/**
	 * Updates the Statistics 
	 */
	public void updateSum(){
		for(AutomatingProof ap : proofList){
			nodeSum+=ap.getNodes();
			branchesSum+=ap.getBranches();
			appliedRulesSum+=ap.getAppliedRules();
			automodeTimeSum+=ap.getTime();
		}
	}
	
	/**
	 * Creates an XLSX File with the result of the evaluation
	 */
	public void createXLS(){
		ExcelManager.generateSingleProjectXLS(this);;
	}
	
}
