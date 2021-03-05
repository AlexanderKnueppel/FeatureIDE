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

import de.ovgu.featureide.core.featurehouse.proofautomation.statistics.ProofStatistics;

/**
 * Abstract class that contains shared functionality of CompleteEvaluation, EvaluationPhase and SingleProject
 * 
 * @author Stefanie
 */
public abstract class Evaluation {
	public static final String FILE_SEPERATOR = System.getProperty("file.separator");
	public Date date;
	//Directory which should be evaluated
	public File toEvaluate;
	public File evaluatePath; //contains a subdirectory Evaluation/date time
	//File where the result of the evaluation is saved
	public File statistics;
	//Statistics used for Evaluation
	public ProofStatistics firstPhase = new ProofStatistics();
	public ProofStatistics secondPhase = new ProofStatistics(); 
	public ProofStatistics firstPhaseReuse = new ProofStatistics(); 
	public ProofStatistics secondPhaseReuse = new ProofStatistics();
	public String verificationType;
	public String method;
	public String evolutionType;
		
	
	public Evaluation(File f){
		toEvaluate = f;
	}
	
	/**
	 * Performs different Steps of the Evaluation
	 */
	public abstract void performEvaluation();
	
	/**
	 * Creates an XLSX file with the statistics of the evaluation
	 */
	public abstract void createXLS();
	
	/**
	 * Sets the statistics file
	 * @param name
	 */
	public void setStatisticsFile(String name){
		statistics = new File (evaluatePath.getAbsolutePath()+FILE_SEPERATOR+name);
	}
	
	/**
	 * Adds the sums of the sub evaluation ev to the current evaluation
	 * @param approachData
	 */
	public void updateStatistics(ApproachData approachData){
		this.firstPhase.addStatistics(approachData.firstPhase);
		this.secondPhase.addStatistics(approachData.secondPhase);
		this.firstPhaseReuse.addStatistics(approachData.firstPhaseReuse);
		this.secondPhaseReuse.addStatistics(approachData.secondPhaseReuse);
	}
	

}
