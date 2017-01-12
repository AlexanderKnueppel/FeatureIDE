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

package de.ovgu.featureide.core.featurehouse.proofautomation.key;

import java.io.File;

import org.eclipse.core.runtime.Assert;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.key4eclipse.starter.core.util.ProofUserManager;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.gui.macros.FinishAbstractProofMacro;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.Proof.Statistics;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.util.MiscTools;

/**
 * An AutomatingProof is used to access the key proof and environment 
 * for FeatureStub and Metaproduct Verification
 * @author Stefanie Bolle
 *
 */
public class AutomatingProof {
	private static final int maxRuleApplications = 100000;
	private KeYEnvironment<?> environment;
	private Contract contract;
	private String typeName;
	private String targetName;
	private String contractName;
	private Proof proof;
	private int nodes;
	private int branches;
	private int appliedRules;
	private long time;
	/**
	 * Constructs a new AutomatingProof 
	 * @param typeName
	 * @param targetName
	 * @param contractName
	 * @param environment
	 * @param contract
	 */
	public AutomatingProof(String typeName, String targetName,String contractName,
             KeYEnvironment<?> environment,Contract contract) {
		Assert.isNotNull(environment);
		Assert.isNotNull(contract);
		this.typeName = typeName;
		this.targetName = targetName;
		this.contractName = contractName;
		this.environment = environment;
		this.contract = contract;
	}
	
	/**
	 * Starts a Proof for the FeatureStub in KeY with prepared Settings 
	 * and with the "Finish abstract proof part" macro
	 * @throws Exception
	 */
	public void startFeatureStubProof() throws Exception{
		try {
			ProofOblInput input = contract.createProofObl(environment.getInitConfig(), contract);
			Assert.isNotNull(input);
			proof = environment.getUi().createProof(environment.getInitConfig(), input);
			Assert.isNotNull(proof);
			ProofUserManager.getInstance().addUser(proof, environment, this);
		} 
		catch (Exception e) {
			 	//ToDo
		}
		// Set proof strategy options
		StrategyProperties sp = prepareSettingsForFeatureStub();
		proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
		// Make sure that the new options are used
		ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(maxRuleApplications);
		ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(sp);
		proof.getSettings().getStrategySettings().setMaxSteps(maxRuleApplications);
		proof.setActiveStrategy(environment.getMediator().getProfile().getDefaultStrategyFactory().create(proof, sp));
		//Apply Macro "Finish abstract proof part"
		FinishAbstractProofMacro fapm = new FinishAbstractProofMacro();
		fapm.applyTo(environment.getMediator(), null, null);
		setStatistics();
	}
	
	/**
	 * Starts a Proof for the Metaproduct Verification with reuseProof for reuse and prepared Settings
	 * @param reuseProof The adapted proof of the FeatureStub phase
	 */
	public void startMetaProductProof(File reuseProof){
		try{
		    ProofOblInput input = contract.createProofObl(environment.getInitConfig(), contract);
		    Assert.isNotNull(input);
		    proof = environment.getUi().createProof(environment.getInitConfig(), input);
		    Assert.isNotNull(proof);
		    ProofUserManager.getInstance().addUser(proof, environment, this);
		}
		catch (Exception e) {
			//ToDo
		}
        StrategyProperties sp = prepareSettingsForMetaproduct();
        proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
        // Make sure that the new options are used
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(maxRuleApplications);
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(sp);
        proof.getSettings().getStrategySettings().setMaxSteps(maxRuleApplications);
        proof.setActiveStrategy(environment.getMediator().getProfile().getDefaultStrategyFactory().create(proof, sp));
        if(reuseProof!=null & reuseProof.getName().endsWith(".proof")){
        	environment.getUi().reuseProof(reuseProof, environment.getMediator());
        }
        KeYUtil.runProofInAutomaticModeWithoutResultDialog(proof);
        setStatistics();
	 }
	 
	 
	/**
	 * Sets the needed statistics (Automode Time, Nodes, Branches, applied Rules) for Evaluation
	 */
	private void setStatistics() {
		Statistics s = proof.statistics();
		setTime((proof != null && !proof.isDisposed()) ? s.autoModeTime : 0l);
		setNodes((proof != null && !proof.isDisposed()) ? s.nodes : 0);
		setBranches((proof != null && !proof.isDisposed()) ? s.branches : 0);
		setAppliedRules((proof != null && !proof.isDisposed()) ? s.totalRuleApps : 0);
	}
	
	/**
	 * Prepares the StrategyPropertys as used for FeatureStub Verification
	 * @return The prepared StrategyProperties
	 */
	private StrategyProperties prepareSettingsForFeatureStub(){
		StrategyProperties sp = proof.getSettings().getStrategySettings().getActiveStrategyProperties();
		sp.setProperty(StrategyProperties.STOPMODE_OPTIONS_KEY, StrategyProperties.STOPMODE_DEFAULT);
		sp.setProperty(StrategyProperties.SPLITTING_OPTIONS_KEY, StrategyProperties.SPLITTING_DELAYED);
		sp.setProperty(StrategyProperties.LOOP_OPTIONS_KEY, StrategyProperties.LOOP_INVARIANT);
		sp.setProperty(StrategyProperties.BLOCK_OPTIONS_KEY, StrategyProperties.BLOCK_CONTRACT);
		sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY, StrategyProperties.METHOD_CONTRACT);
		sp.setProperty(StrategyProperties.DEP_OPTIONS_KEY, StrategyProperties.DEP_OFF);
		sp.setProperty(StrategyProperties.QUERY_OPTIONS_KEY, StrategyProperties.QUERY_RESTRICTED);
		sp.setProperty(StrategyProperties.QUERYAXIOM_OPTIONS_KEY, StrategyProperties.QUERYAXIOM_OFF);
		sp.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, StrategyProperties.NON_LIN_ARITH_NONE);
		sp.setProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY, StrategyProperties.QUANTIFIERS_NON_SPLITTING_WITH_PROGS);
		sp.setProperty(StrategyProperties.CLASS_AXIOM_OPTIONS_KEY, StrategyProperties.CLASS_AXIOM_DELAYED);
		sp.setProperty(StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY, StrategyProperties.AUTO_INDUCTION_OFF);
		return sp;
	}
	
	/**
	 * Prepares the StrategyPropertys as used for Metaproduct Verification
	 * @return The prepared StrategyProperties
	 */	
	private StrategyProperties prepareSettingsForMetaproduct(){
		StrategyProperties sp = proof.getSettings().getStrategySettings().getActiveStrategyProperties();
		sp.setProperty(StrategyProperties.STOPMODE_OPTIONS_KEY, StrategyProperties.STOPMODE_DEFAULT);
		sp.setProperty(StrategyProperties.SPLITTING_OPTIONS_KEY, StrategyProperties.SPLITTING_DELAYED);
		sp.setProperty(StrategyProperties.LOOP_OPTIONS_KEY, StrategyProperties.LOOP_INVARIANT);
		sp.setProperty(StrategyProperties.BLOCK_OPTIONS_KEY, StrategyProperties.BLOCK_CONTRACT);
		sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY, StrategyProperties.METHOD_CONTRACT);
		sp.setProperty(StrategyProperties.DEP_OPTIONS_KEY, StrategyProperties.DEP_ON);
		sp.setProperty(StrategyProperties.QUERY_OPTIONS_KEY, StrategyProperties.QUERY_ON);
		sp.setProperty(StrategyProperties.QUERYAXIOM_OPTIONS_KEY, StrategyProperties.QUERYAXIOM_ON);
		sp.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, StrategyProperties.NON_LIN_ARITH_DEF_OPS);
		sp.setProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY, StrategyProperties.QUANTIFIERS_NON_SPLITTING_WITH_PROGS);
		sp.setProperty(StrategyProperties.CLASS_AXIOM_OPTIONS_KEY, StrategyProperties.CLASS_AXIOM_FREE);
		sp.setProperty(StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY, StrategyProperties.AUTO_INDUCTION_OFF);
		return sp;
	}
	
	/**
	 * Saves the proof in the given file
	 * @param proofFile
	 */
	public void saveProof(String path){
		final String defaultName 
    	= MiscTools.toValidFileName(environment.getMediator()
    		.getSelectedProof().name()
            .toString());
		File proofFile = new File (path+System.getProperty("file.separator")+defaultName+".proof");
		MainWindow w = MainWindow.getInstance();
		w.saveProof(proofFile);
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
	 * Returns the Number of Nodes 
	 * @return nodes
	 */
	public int getNodes() {
		return nodes;
	}
	
	/**
	 * Sets the Number of Nodes
	 * @param nodes
	 */
	private void setNodes(int nodes) {
		this.nodes = nodes;
	}
	
	/**
	 * Returns the Number of Branches
	 * @return branches
	 */
	public int getBranches() {
		return branches;
	}
	
	/**
	 * Sets the Number of Branches
	 * @param branches
	 */
	private void setBranches(int branches) {
		this.branches = branches;
	}
	
	/**
	 * Returns the Automode time of the proof
	 * @return time
	 */
	public long getTime() {
		return time;
	}
	
	/**
	 * Sets the Automode time of the proof
	 * @param time
	 */
	private void setTime(long time) {
		this.time = time;
	}
	
	/**
	 * Returns the applied Rules of the Proof
	 * @return appliedRules
	 */
	public int getAppliedRules(){
		return appliedRules;
	}
	
	/**
	 * Sets the applied Rules
	 * @param appliedRules
	 */
	private void setAppliedRules(int appliedRules){
		this.appliedRules = appliedRules;
	}
}
