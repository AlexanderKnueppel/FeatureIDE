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

/**
 * TODO description
 * 
 * @author Stefanie
 */
public abstract class Evaluation {
	public static final String FILE_SEPERATOR = System.getProperty("file.separator");
	public File toEvaluate;
	public File statistics;
	public int nodeSum=0;
	public int branchesSum=0;
	public int appliedRulesSum=0;
	public long automodeTimeSum=0;
	
	public abstract void performEvaluation();
	
	public abstract void createXLS();
	
	public void setStatisticsFile(String name){
		statistics = new File (toEvaluate.getAbsolutePath()+FILE_SEPERATOR+name);
	}
}
