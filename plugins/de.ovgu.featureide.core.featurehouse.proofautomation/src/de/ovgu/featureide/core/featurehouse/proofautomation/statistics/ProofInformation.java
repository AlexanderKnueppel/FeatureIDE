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
package de.ovgu.featureide.core.featurehouse.proofautomation.statistics;

/**
 * TODO description
 * 
 * @author marlen
 */
public class ProofInformation {
	private String typeName;
	private String targetName;
	private ProofStatistics stat = new ProofStatistics();
	private ProofStatistics reusedStat = new ProofStatistics();
	private boolean closed = false;
	private String featurestub;
	/**
	 * 
	 * @param type
	 * @param target
	 * @param stat
	 * @param reusedStat
	 * @param closed
	 */
	public ProofInformation(String type, String target, String featurestub, ProofStatistics stat, ProofStatistics reusedStat, boolean closed) {
		this.typeName = type;
		this.targetName = target;
		this.featurestub =featurestub;
		this.stat = stat;
		this.reusedStat = reusedStat;
		this.closed = closed;
	}
	
	
	/**
	 * Returns the type
	 * @return type
	 */
	public String getTypeName(){
		return typeName;
	}
	
	/**
	 * Returns the target
	 * @return target
	 */
	public String getTargetName(){
		return targetName;
	}
	
	/**
	 * @return the featurestub
	 */
	public String getFeaturestub() {
		return featurestub;
	}

	/**
	 * @param featurestub the featurestub to set
	 */
	public void setFeaturestub(String featurestub) {
		this.featurestub = featurestub;
	}
	/**
	 * @return the stat
	 */
	public ProofStatistics getStat() {
		return stat;
	}

	/**
	 * @return the reusedStat
	 */
	public ProofStatistics getReusedStat() {
		return reusedStat;
	}
	
	/**
	 * @return the closed
	 */
	public boolean isClosed() {
		return closed;
	}
	

}
