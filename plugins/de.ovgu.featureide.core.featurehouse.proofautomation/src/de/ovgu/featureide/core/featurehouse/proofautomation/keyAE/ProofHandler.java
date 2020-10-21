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
package de.ovgu.featureide.core.featurehouse.proofautomation.keyAE;

import java.io.File;
import java.io.IOException;
import java.util.Set;

import de.ovgu.featureide.core.featurehouse.proofautomation.model.ProofStatistics;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.Statistics;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.util.MiscTools;

/**
 * TODO description
 * 
 * @author marlen
 */
public class ProofHandler {
	private KeYEnvironment<?> environment;
	private Contract contract;
	private String typeName;
	private String targetName;
	private Proof proof;
	private String featurestub;
	private ProofStatistics stat = new ProofStatistics();
	private boolean closed = false;
	/**
	 * Constructs a new AutomatingProof 
	 * @param typeName
	 * @param targetName
	 * @param contractName
	 * @param environment
	 * @param contract
	 */
	public ProofHandler(String typeName, String targetName,String contractName,
             KeYEnvironment<?> environment,Contract contract) {
		this.typeName = typeName;
		this.targetName = targetName;
		this.environment = environment;
		this.contract = contract;
	}
	
	/**
	 * Returns the target
	 * @return target
	 */
	public String getTargetName(){
		return targetName;
	}
	public Proof getProof(){
		return proof;
	}
	
	public void setProof(Proof proof) {
		this.proof = proof;
	}
	
	public KeYEnvironment<?> getEnvironment(){
		return environment;
	}

	public Contract getContract() {
		return contract;
	}
	/**
	 * Returns the type
	 * @return type
	 */
	public String getTypeName(){
		return typeName;
	}
	
	/**
	 * Saves the proof in the given file
	 * @param proofFile
	 */
	public File saveProof(String path){
		final String defaultName = MiscTools.toValidFileName(proof.name().toString());
		File proofFile = new File(path+System.getProperty("file.separator")+defaultName+".proof");
		try {
			proof.saveToFile(proofFile);
		} catch (IOException e) {
			e.printStackTrace();
		}
		return proofFile;
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
	 * Sets the needed statistics (Automode Time, Nodes, Branches, applied Rules) for Evaluation
	 */
	public void setStatistics() {
		Statistics s = proof.getStatistics();
		stat.setAutomodeTime((proof != null && !proof.isDisposed()) ? s.autoModeTimeInMillis : 0l);
		stat.setNodes((proof != null && !proof.isDisposed()) ? s.nodes : 0);
		stat.setBranches((proof != null && !proof.isDisposed()) ? s.branches : 0);
		stat.setAppliedRules((proof != null && !proof.isDisposed()) ? s.totalRuleApps : 0);
	}
	
	/**
	 * @return the closed
	 */
	public boolean isClosed() {
		return closed;
	}
	/**
	 * 
	 * @param closed
	 */
	public void setClosed(boolean closed) {
		this.closed = closed;
	}
}

