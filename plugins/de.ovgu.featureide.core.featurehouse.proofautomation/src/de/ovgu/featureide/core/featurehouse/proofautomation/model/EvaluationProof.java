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

/**
 * TODO description
 * 
 * @author Stefanie
 */
public class EvaluationProof {
	private String type;
	private String target;
	private ProofStatistics sum;
	private ProofStatistics reusedSum;
	private int count;
	private boolean closed;
	
	public EvaluationProof(String target, String type){
		this.type = type;
		this.target = target;
		sum = new ProofStatistics();
		reusedSum = new ProofStatistics();
		count = 0;
		closed = true;
	}
	
	public void increaseCount(){
		count++;
	}
	
	public void addSum(ProofStatistics s, ProofStatistics r){
		this.sum.addStatistics(s);
		this.reusedSum.addStatistics(r);
	}
	/**
	 * @return the sum
	 */
	public ProofStatistics getSum() {
		return sum;
	}
	/**
	 * @return the reusedSum
	 */
	public ProofStatistics getReusedSum() {
		return reusedSum;
	}

	/**
	 * @param sum the sum to set
	 */
	public void setSum(ProofStatistics sum) {
		this.sum = sum;
	}
	/**
	 * @return the type
	 */
	public String getType() {
		return type;
	}
	/**
	 * @return the target
	 */
	public String getTarget() {
		return target;
	}

	/**
	 * @return the count
	 */
	public int getCount() {
		return count;
	}

	/**
	 * @param closed the closed to set
	 */
	public void setClosed(boolean closed) {
		this.closed = closed;
	}

	/**
	 * @return
	 */
	public boolean isClosed() {
		return closed;
	}
}
