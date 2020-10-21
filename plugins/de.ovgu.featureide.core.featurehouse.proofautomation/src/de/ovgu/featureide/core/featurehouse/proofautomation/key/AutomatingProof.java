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
import java.io.IOException;
import java.nio.file.FileSystem;
import java.nio.file.FileSystems;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.Set;

import de.ovgu.featureide.core.featurehouse.proofautomation.model.ProofStatistics;
import org.key_project.util.collection.ImmutableList;
//import org.key_project.key4eclipse.starter.core.util.ProofUserManager;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.macros.CompleteAbstractProofMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.Statistics;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.consistency.AbstractFileRepo;
import de.uka.ilkd.key.proof.io.consistency.SimpleFileRepo;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
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
	private ProofStatistics stat = new ProofStatistics();
	private ProofStatistics reusedStat = new ProofStatistics();
	private String featurestub;
	private boolean closed = false;
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
	 * Initializes a proof just to get all evaluation information
	 */
	public AutomatingProof(String type, String target,int nodes, int branches, int appliedRules, 
			long time,int reusedNodes, int reusedBranches, int reusedAppliedRules, long reusedTime,boolean closed) {
		this.typeName = type;
		this.targetName = target;
		this.stat = new ProofStatistics(nodes,branches,appliedRules,time);
		this.reusedStat = new ProofStatistics(reusedNodes,reusedBranches,reusedAppliedRules,reusedTime);
		this.closed = closed;
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
			proof = environment.createProof(input);
			waitForNewThread(threadsBefore);
			
			threadsBefore = Thread.getAllStackTraces().keySet();
			// Set proof strategy options
			proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
			waitForNewThread(threadsBefore);
			
			threadsBefore = Thread.getAllStackTraces().keySet();
			// Make sure that the new options are used
			ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(maxRuleApplication);
			waitForNewThread(threadsBefore);
			
			threadsBefore = Thread.getAllStackTraces().keySet();
			ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(sp);
			waitForNewThread(threadsBefore);
			
			threadsBefore = Thread.getAllStackTraces().keySet();
			proof.getSettings().getStrategySettings().setMaxSteps(maxRuleApplication);
	        proof.setActiveStrategy(proof.getServices().getProfile().getDefaultStrategyFactory().create(proof, sp));
	        waitForNewThread(threadsBefore);
	        
	        ProofControl proofControl = environment.getUi().getProofControl();
			int previousNodes;
			do{
				previousNodes = proof.countNodes();
				
				threadsBefore = Thread.getAllStackTraces().keySet();
				
				proofControl.runMacro(proof.root(), new CompleteAbstractProofMacro(), null);
				proofControl.waitWhileAutoMode();
				
				waitForNewThread(threadsBefore);
			}while(proof.countNodes()==previousNodes);
	        if(proof.openGoals().isEmpty()){
	            System.out.println("AutomationProof Line 146 : Contract '" + contract.getDisplayName() + "' of " + contract.getTarget() + " is " + (closed ? "verified" : "still open") + ".");
	        	closed = true;
	        }

        setStatistics();
		} 
		catch (ProofInputException e) {
            System.out.println("Exception at '" + contract.getDisplayName() + "' of " + contract.getTarget() + ":");
            e.printStackTrace();
		}

	}
	
	/**
	 * Starts a Proof for the Metaproduct Verification with reuseProof for reuse and prepared Settings
	 * @param reuseProof The adapted proof of the FeatureStub phase
	 */
	public boolean startMetaProductProof(File reuseProof, StrategyProperties sp, int maxRuleApplication, String savePath){
		System.out.println("AutomatingProof Line 143 : Starte Metaprodukt Beweis");
		
		boolean reusedAProof = false;
		try{
		    proof = environment.createProof(contract.createProofObl(environment.getInitConfig(), contract));
		}
		catch (ProofInputException e) {
			e.printStackTrace();
		}
		
//		ImmutableSet<Contract> contracts = environment.getSpecificationRepository().getAllContracts();
//		for (Contract contract : contracts) {
//        	System.out.println(contract.getName());
//		}
        ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
		HashMap<String,String> choices = proof.getSettings().getChoiceSettings().getDefaultChoices();
        choices.put("assertions", "assertions:safe");
        choiceSettings.setDefaultChoices(choices);
           
        if(reuseProof!=null){
	        if(reuseProof.getName().endsWith(".proof")){
	        	UserInterfaceControl userInterface = new DefaultUserInterfaceControl(null);
	        	KeYEnvironment<UserInterfaceControl> keYEnvironment = null;
	            try {
	            	AbstractProblemLoader loader = userInterface.load(null, reuseProof, null, null, null, null, false);
	            	InitConfig initConfig = loader.getInitConfig();
	            	keYEnvironment = new KeYEnvironment<>(userInterface, initConfig, loader.getProof(), loader.getProofScript(), loader.getResult());
	            	Proof proof2 = keYEnvironment.getLoadedProof();
	            	
	            	System.out.println("AutomatingProof Line 193 : Reused Proof -> " + proof2.name().toString());
	            	
	            	keYEnvironment.getProofControl().runMacro(proof2.root(),new CompleteAbstractProofMacro(), null);
	            	keYEnvironment.getProofControl().waitWhileAutoMode();
	            	reusedAProof = true;

				} catch (ProblemLoaderException e) {
					System.out.println("Loading the File " + reuseProof.toString() + " failed in Method startMetaProductProof");
					e.printStackTrace();
				}	
	            setProof(keYEnvironment.getLoadedProof());
	            File reusedProof = saveProof(savePath);
            	try {
					environment.load(reusedProof);
				} catch (ProblemLoaderException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
            	reusedProof.delete();
				setReusedStatistics();
	        	
	        }
	       System.out.println("Reused: " + proof.getStatistics());
	    }
        

        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(maxRuleApplication);
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(sp);
        proof.getSettings().getStrategySettings().setMaxSteps(maxRuleApplication);
        proof.setActiveStrategy(environment.getProfile().getDefaultStrategyFactory().create(proof, sp));

        //deactivateResultDialog();

        while(!proof.openEnabledGoals().isEmpty()&&goalHasApplicableRules()){
        	int previousNodes = proof.countNodes();
        	environment.getProofControl().startAndWaitForAutoMode(proof);
        	if(uncloseableGoal(previousNodes)){
        		break;
        	}
        }
        closed = true;
        if(!proof.openGoals().isEmpty()){
        	System.out.println(this.targetName+this.typeName+" was not closed");
        	closed = false;
        }
        setStatistics();
        
        System.out.println("Actual: " + proof.getStatistics());
        
        return reusedAProof;
	 }
	
	public boolean goalHasApplicableRules(){
		ImmutableList<Goal> goals = proof.openGoals();
		for(Goal g: goals){
			if(SymbolicExecutionUtil.hasApplicableRules(g)){
				return true;
			}
		}
		return false;
	}
	
	public boolean uncloseableGoal(int previousNodes){
		return proof.countNodes()==previousNodes;
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
	 
	private void deactivateResultDialog(){
		NotificationTask task= null;
		task = MainWindow.getInstance().getNotificationManager().getNotificationTask(NotificationEventID.PROOF_CLOSED);
        if (task != null) {
           MainWindow.getInstance().getNotificationManager().removeNotificationTask(task);
        }
	}
	*/ 
	
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
	 * Sets the needed reused statistics (Automode Time, Nodes, Branches, applied Rules) for Evaluation
	 */
	public void setReusedStatistics() {
		Statistics s = proof.getStatistics();
		reusedStat.setAutomodeTime((proof != null && !proof.isDisposed()) ? s.autoModeTimeInMillis : 0l);
		reusedStat.setNodes((proof != null && !proof.isDisposed()) ? s.nodes : 0);
		reusedStat.setBranches((proof != null && !proof.isDisposed()) ? s.branches : 0);
		reusedStat.setAppliedRules((proof != null && !proof.isDisposed()) ? s.totalRuleApps : 0);
	}
	
	/**
	 * Saves the proof in the given file
	 * @param proofFile
	 */
	public File saveProof(String path){
		System.out.println("AutomatingProof Zeile 314 : Saving proof " + proof.name().toString());
		final String defaultName = MiscTools.toValidFileName(proof.name().toString());
		File proofFile = new File(path+System.getProperty("file.separator")+defaultName+".proof");

		Set<Thread> threadsBefore = Thread.getAllStackTraces().keySet();
		try {
			proof.saveToFile(proofFile);

		} catch (IOException e) {
			e.printStackTrace();
		}
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
	
	public Proof getProof(){
		return proof;
	}
	
	public void setProof(Proof proof) {
		this.proof = proof;
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
	 * @return the closed
	 */
	public boolean isClosed() {
		return closed;
	}
	
	public void removeProof(){
		proof.dispose();
		//environment.getLoadedProof().dispose();
	}

	/**
	 * @param oldPartialProof
	 * @param maxRuleApplication
	 * @param defaultSettingsForFeatureStub
	 */
	public void replayFeatureStubProof(File oldPartialProof, String savePath, int maxRuleApplication,
			StrategyProperties defaultSettingsForFeatureStub) {
		boolean reusedAProof = false;
		try{
		    ProofOblInput input = contract.createProofObl(environment.getInitConfig(), contract);
		    proof = environment.getUi().createProof(environment.getInitConfig(), input);
		}
		catch (Exception e) {
			e.printStackTrace();
		}
		HashMap<String,String> choices = proof.getSettings().getChoiceSettings().getDefaultChoices();
        choices.put("assertions", "assertions:safe");
        ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
        choiceSettings.setDefaultChoices(choices);
        if(oldPartialProof!=null){
	        if(oldPartialProof.getName().endsWith(".proof")){
	        	UserInterfaceControl userInterface = new DefaultUserInterfaceControl(null);
	        	KeYEnvironment<UserInterfaceControl> keYEnvironment = null;
	            try {
	            	AbstractProblemLoader loader = userInterface.load(null, oldPartialProof, null, null, null, null, false);
	            	InitConfig initConfig = loader.getInitConfig();
	            	keYEnvironment = new KeYEnvironment<>(userInterface, initConfig, loader.getProof(), loader.getProofScript(), loader.getResult());
	            	Proof proof2 = keYEnvironment.getLoadedProof();
	            	
	            	System.out.println("AutomatingProof Line 193 : Reused Proof -> " + proof2.name().toString());
	            	
	            	keYEnvironment.getProofControl().runMacro(proof2.root(),new CompleteAbstractProofMacro(), null);
	            	keYEnvironment.getProofControl().waitWhileAutoMode();
	            	reusedAProof = true;

				} catch (ProblemLoaderException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}	
	            
	            File reusedProof = saveProof(savePath);
            	try {
					environment.load(reusedProof);
				} catch (ProblemLoaderException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
            	reusedProof.delete();
				setProof(keYEnvironment.getLoadedProof());
				setReusedStatistics();
	        	
	        }
        }
	}

}
