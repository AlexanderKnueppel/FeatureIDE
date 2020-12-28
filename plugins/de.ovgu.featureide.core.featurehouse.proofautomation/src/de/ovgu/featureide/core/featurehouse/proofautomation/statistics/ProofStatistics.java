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
 * Class for saving the Statistics
 * 
 * @author Stefanie
 */
public class ProofStatistics {
	private int nodes=0;
	private int branches=0;
	private int appliedRules=0;
	private long automodeTime=0;
	
	public ProofStatistics(int nodeSum, int branchesSum, int appliedRulesSum, long automodeTimeSum){
		this.nodes= nodeSum;
		this.branches = branchesSum;
		this.appliedRules = appliedRulesSum;
		this.automodeTime = automodeTimeSum;
	}
	
	/**
	 * 
	 */
	public ProofStatistics() {
		this.nodes= 0;
		this.branches = 0;
		this.appliedRules = 0;
		this.automodeTime = 0;
	}
	
	public void reset(){
		this.nodes= 0;
		this.branches = 0;
		this.appliedRules = 0;
		this.automodeTime = 0;
	}

	public void addStatistics(ProofStatistics toAdd){
		this.nodes+=toAdd.nodes;
		this.branches+=toAdd.branches;
		this.appliedRules+=toAdd.appliedRules;
		this.automodeTime+=toAdd.automodeTime;
	}
	
	public void removeStatistics(ProofStatistics toAdd){
		this.nodes-=toAdd.nodes;
		this.branches-=toAdd.branches;
		this.appliedRules-=toAdd.appliedRules;
		this.automodeTime-=toAdd.automodeTime;
	}
	/**
	 * @return the nodeSum
	 */
	public int getNodes() {
		return nodes;
	}
	/**
	 * @param nodeSum the nodeSum to set
	 */
	public void setNodes(int nodes) {
		this.nodes = nodes;
	}
	/**
	 * @return the branchesSum
	 */
	public int getBranches() {
		return branches;
	}
	/**
	 * @param branchesSum the branchesSum to set
	 */
	public void setBranches(int branches) {
		this.branches = branches;
	}
	/**
	 * @return the appliedRulesSum
	 */
	public int getAppliedRules() {
		return appliedRules;
	}
	/**
	 * @param appliedRulesSum the appliedRulesSum to set
	 */
	public void setAppliedRules(int appliedRules) {
		this.appliedRules = appliedRules;
	}
	/**
	 * @return the automodeTimeSum
	 */
	public long getAutomodeTime() {
		return automodeTime;
	}
	/**
	 * @param automodeTimeSum the automodeTimeSum to set
	 */
	public void setAutomodeTime(long automodeTime) {
		this.automodeTime = automodeTime;
	}
	
	public String toString(){
		String stat = "Nodes:   "+ this.nodes+"\n";
		stat +="Branches:  "+this.branches+"\n";
		stat+= "Applied Rules:"+this.appliedRules+"\n";
		stat+= "Automode Time:"+this.automodeTime+"\n";
		return stat;
	}
}
