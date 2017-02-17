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
import java.util.HashMap;
import java.util.Set;

//import org.key_project.key4eclipse.starter.core.util.ProofUserManager;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.gui.macros.FinishAbstractProofMacro;
import de.uka.ilkd.key.gui.notification.NotificationEventID;
import de.uka.ilkd.key.gui.notification.NotificationTask;
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
 * @author Stefanie
 *
 */
public class AutomatingProof {
	private KeYEnvironment<?> environment;
	private Contract contract;
	private String typeName;
	private String targetName;
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
		this.typeName = typeName;
		this.targetName = targetName;
		this.environment = environment;
		this.contract = contract;
	}
	
	/**
	 * Initalizes a proof just to get all evaluation information
	 */
	public AutomatingProof(String type, String target,int nodes, int branches, int appliedRules, long time) {
		this.typeName = type;
		this.targetName = target;
		this.nodes= nodes;
		this.branches = branches;
		this.appliedRules = appliedRules;
		this.time = time;
	}
	
	/**
	 * Starts a Proof for the FeatureStub in KeY with prepared Settings 
	 * and with the "Finish abstract proof part" macro
	 * @throws Exception
	 */
	public void startAbstractProof(int maxRuleApplication, StrategyProperties sp) throws Exception{
		try {
			Set<Thread> threadsBefore = Thread.getAllStackTraces().keySet();
			ProofOblInput input = contract.createProofObl(environment.getInitConfig(), contract);
			proof = environment.getUi().createProof(environment.getInitConfig(), input);
			waitForNewThread(threadsBefore);
		} 
		catch (Exception e) {
			 	//ToDo
		}
		// Set proof strategy options
		Set<Thread> threadsBefore = Thread.getAllStackTraces().keySet();
		proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
		waitForNewThread(threadsBefore);
		// Make sure that the new options are used
		threadsBefore = Thread.getAllStackTraces().keySet();
		ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(maxRuleApplication);
		waitForNewThread(threadsBefore);
		threadsBefore = Thread.getAllStackTraces().keySet();
		ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(sp);
		waitForNewThread(threadsBefore);
		proof.getSettings().getStrategySettings().setMaxSteps(maxRuleApplication);
		proof.setActiveStrategy(environment.getMediator().getProfile().getDefaultStrategyFactory().create(proof, sp));
		//Apply Macro "Finish abstract proof part"
		FinishAbstractProofMacro fapm = new FinishAbstractProofMacro();
		threadsBefore = Thread.getAllStackTraces().keySet();
		fapm.applyTo(environment.getMediator(), null, null);
		waitForNewThread(threadsBefore);
		setStatistics();
	}
	
	/**
	 * Starts a Proof for the Metaproduct Verification with reuseProof for reuse and prepared Settings
	 * @param reuseProof The adapted proof of the FeatureStub phase
	 */
	public boolean startMetaProductProof(File reuseProof, StrategyProperties sp, int maxRuleApplication){
		boolean reusedAProof = false;
		Set<Thread> threadsBeforeStart = Thread.getAllStackTraces().keySet();
		try{
			Set<Thread> threadsBefore = Thread.getAllStackTraces().keySet();
		    ProofOblInput input = contract.createProofObl(environment.getInitConfig(), contract);
		    proof = environment.getUi().createProof(environment.getInitConfig(), input);
//		    ProofUserManager.getInstance().addUser(proof, environment, this);
		    waitForNewThread(threadsBefore);
		}
		catch (Exception e) {
			e.printStackTrace();
		}
		waitForNewThread(threadsBeforeStart);
		Set<Thread>threadsBefore = Thread.getAllStackTraces().keySet();
		HashMap<String,String> choices = proof.getSettings().getChoiceSettings().getDefaultChoices();
		waitForNewThread(threadsBefore);
	    threadsBefore = Thread.getAllStackTraces().keySet();
        choices.put("assertions", "assertions:safe");
        waitForNewThread(threadsBefore);
        threadsBefore = Thread.getAllStackTraces().keySet();
        MainWindow.getInstance().getMediator().getSelectedProof().getSettings().getChoiceSettings().setDefaultChoices(choices);
        waitForNewThread(threadsBefore);
        if(reuseProof!=null){
	        if(reuseProof.getName().endsWith(".proof")){
	        	threadsBefore =Thread.getAllStackTraces().keySet();
	        	MainWindow.getInstance().reuseProof(reuseProof);
	        	waitForNewThread(threadsBefore);
	        	reusedAProof = true;
	        }
	    }
        waitForNewThread(threadsBeforeStart);
        threadsBefore = Thread.getAllStackTraces().keySet();
        try{
        MainWindow.getInstance().getMediator().getSelectedProof().getSettings().getStrategySettings().setActiveStrategyProperties(sp);
        }
        catch(Exception e){
        	e.printStackTrace();
        }
        waitForNewThread(threadsBefore);
        threadsBefore = Thread.getAllStackTraces().keySet();
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(maxRuleApplication);
        waitForNewThread(threadsBefore);
        threadsBefore = Thread.getAllStackTraces().keySet();
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(sp);
        waitForNewThread(threadsBefore);
        threadsBefore = Thread.getAllStackTraces().keySet();
        proof.getSettings().getStrategySettings().setMaxSteps(maxRuleApplication);
        waitForNewThread(threadsBefore);
        threadsBefore = Thread.getAllStackTraces().keySet();
        proof.setActiveStrategy(environment.getMediator().getProfile().getDefaultStrategyFactory().create(proof, sp));
        waitForNewThread(threadsBefore);
        threadsBefore = Thread.getAllStackTraces().keySet();
        MainWindow.getInstance().getMediator().getSelectedProof().setActiveStrategy(environment.getMediator().getProfile().getDefaultStrategyFactory().create(proof, sp));
        waitForNewThread(threadsBefore);
        threadsBefore = Thread.getAllStackTraces().keySet();
        deactivateResultDialog();
        waitForNewThread(threadsBefore);
        threadsBefore = Thread.getAllStackTraces().keySet();
        MainWindow.getInstance().getMediator().startAutoMode();
        waitForNewThread(threadsBefore);
        setStatistics();
        return reusedAProof;
	 }

	/**
	 * Waits for termination of all threads, which were started after threadsBefore
	 * necessary in key to avoid concurrent modification exception
	 * @param threadsBefore
	 */
	public void waitForNewThread(Set<Thread> threadsBefore){
		Set<Thread> mafter =Thread.getAllStackTraces().keySet();
    	for(Thread t1: mafter){
    		if(!threadsBefore.contains(t1)){
    			while(t1.isAlive());
    		}
    	}
	}
	
	/**
	 * Deactivates the result dialog which popups in key when a proof is finished
	 */
	private void deactivateResultDialog(){
		NotificationTask task= null;
		task = MainWindow.getInstance().getNotificationManager().getNotificationTask(NotificationEventID.PROOF_CLOSED);
        if (task != null) {
           MainWindow.getInstance().getNotificationManager().removeNotificationTask(task);
        }
	}
	 
	/**
	 * Sets the needed statistics (Automode Time, Nodes, Branches, applied Rules) for Evaluation
	 */
	public void setStatistics() {
		Statistics s = proof.statistics();
		setTime((proof != null && !proof.isDisposed()) ? s.autoModeTime : 0l);
		setNodes((proof != null && !proof.isDisposed()) ? s.nodes : 0);
		setBranches((proof != null && !proof.isDisposed()) ? s.branches : 0);
		setAppliedRules((proof != null && !proof.isDisposed()) ? s.totalRuleApps : 0);
	}
	
	/**
	 * Saves the proof in the given file
	 * @param proofFile
	 */
	public File saveProof(String path){
		final String defaultName 
    	= MiscTools.toValidFileName(environment.getMediator()
    		.getSelectedProof().name()
            .toString());
		File proofFile = new File (path+System.getProperty("file.separator")+defaultName+".proof");
		MainWindow w = MainWindow.getInstance();
		Set<Thread> threadsBefore = Thread.getAllStackTraces().keySet();
		w.saveProof(proofFile);
		waitForNewThread(threadsBefore);
		return proofFile;
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
	
	public Proof getProof(){
		return proof;
	}
	
	public void setProof(Proof proof) {
		this.proof = proof;
	}
}
