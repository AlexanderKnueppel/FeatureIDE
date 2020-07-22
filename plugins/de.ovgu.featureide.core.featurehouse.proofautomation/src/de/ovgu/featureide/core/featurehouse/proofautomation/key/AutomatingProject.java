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
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.ovgu.featureide.core.featurehouse.proofautomation.builder.BuilderUtil;
import de.ovgu.featureide.core.featurehouse.proofautomation.builder.FeatureStubBuilder;
import de.ovgu.featureide.core.featurehouse.proofautomation.builder.MetaProductBuilder;
import de.ovgu.featureide.core.featurehouse.proofautomation.configuration.Configuration;
import de.ovgu.featureide.core.featurehouse.proofautomation.filemanagement.FileManager;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.ClassTree;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
/**
 * This class performs the proofs for a complete project
 * 
 * @author Stefanie
 */
public class AutomatingProject{
	public static final AutomatingProject automatingProject = new AutomatingProject();
	
	private static final String FILE_SEPERATOR = System.getProperty("file.separator");
	private List<AutomatingProof> proofList; //contains all proofs of the current project
	private List<AutomatingProof> phase1ProofList = new LinkedList<AutomatingProof>();
	private List<AutomatingProof> proofListWithPhase1And2 = new LinkedList<AutomatingProof>();
	private int maxRuleApplication = Configuration.maxRuleApplication; // sets the maximal number of rules to be applicated on one proof
	
	public static AutomatingProject getInstance(){
		return automatingProject;
	}
	
	public List<AutomatingProof> getProofList(){
		return proofList;
	}
	
	/**
	 * @return the phase1ProofList
	 */
	public List<AutomatingProof> getPhase1ProofList() {
		return phase1ProofList;
	}

	/**
	 * @return the proofListWithPhase1And2
	 */
	public List<AutomatingProof> getProofListWithPhase1And2() {
		return proofListWithPhase1And2;
	}

	/**
	 * @param phase1ProofList the phase1ProofList to set
	 */
	public void setPhase1ProofList(List<AutomatingProof> phase1ProofList) {
		this.phase1ProofList = phase1ProofList;
	}

	public void setMaxRuleApplication(int mra){
		this.maxRuleApplication = mra;
	}
	
	/**
	 * Performs the evaluation of approach 1 Fefalution + Family Proof Replay
	 * @param loc
	 */
	public void performVa0(File loc, File evalPath){
		boolean firstVersion = loc.getName().contains("1");
		if(!firstVersion){
			FileManager.reuseFeaturestub(evalPath, loc);
		}
		performFeaturestubVerification(loc,evalPath,firstVersion, true); //TODO run with false
		FileManager.copySavedProofsToPartialProofs(evalPath);
		MetaProductBuilder.preparePartialProofs(loc,evalPath);

		performMetaproductVerification(loc,evalPath);
	}
	
	/**
	 * Performs the evaluation of approach 1 Fefalution
	 * @param loc
	 */
	public void performVa1(File loc, File evalPath){
//		File transactionAccount = new File(loc.getAbsolutePath()+FILE_SEPERATOR+FileManager.featureStubDir+FILE_SEPERATOR+"Transaction"+FILE_SEPERATOR+"Account.java");
//		File lockAccount = new File(loc.getAbsolutePath()+FILE_SEPERATOR+FileManager.featureStubDir+FILE_SEPERATOR+"Lock"+FILE_SEPERATOR+"Account.java");
//		FeatureStubBuilder.prepareForVerification(transactionAccount,lockAccount);
		boolean firstVersion = loc.getName().contains("1");
		if(!firstVersion){
			FileManager.reuseFeaturestub(evalPath, loc);
		}
		performFeaturestubVerification(loc,evalPath,firstVersion, false); //TODO run with false
		FileManager.copySavedProofsToPartialProofs(evalPath);
		MetaProductBuilder.preparePartialProofs(loc,evalPath);
//		
//		if(loc.getName().contains("5") || loc.getName().contains("6")) {
//			File acc = new File(loc.getAbsolutePath()+FILE_SEPERATOR+FileManager.metaproductDir+FILE_SEPERATOR+"Account.java");
//			BuilderUtil.fixUpdateLoggingInBA5BA6(acc);
//		}
		performMetaproductVerification(loc,evalPath);
	}
	
	/**
	 * Performs the evaluation of approach 2 Metaproduct
	 * @param loc
	 */
	public void performVa2(File loc,File evalPath){
		//Phase 1
		String savePartialProofsPath = evalPath.getAbsolutePath()+FILE_SEPERATOR+FileManager.partialProofsDir;
		boolean firstVersion =loc.getName().contains("1");
		if(!firstVersion){
			File version1 = new File(FileManager.getProjectv1Path(evalPath).getAbsolutePath()+FILE_SEPERATOR+FileManager.partialProofsDir);
			FileManager.copyFolderContent(version1,new File(savePartialProofsPath));
		}
		File metaproduct = getMetaproduct(loc);
		List<AutomatingProof> abstractProofs = loadInKeY(metaproduct);
		phase1ProofList.addAll(abstractProofs);
		List<File> abstractProofPart = new LinkedList<File>();
		for(AutomatingProof a : abstractProofs){
			try {
				File reuseProof = null;
				if(!firstVersion){
					reuseProof = proofAlreadyExistsAbstract(a,evalPath);
				}
				if(reuseProof!=null){
					abstractProofPart.add(reuseProof);
				}
				else{
					a.startAbstractProof(maxRuleApplication, DefaultStrategies.defaultSettingsForFeatureStub());
					abstractProofPart.add(a.saveProof(savePartialProofsPath));
				}
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		
		for(File absProof: abstractProofPart) {
			System.out.println("[" + absProof.getName() + " ("+absProof.getAbsolutePath()+")]");
		}
		
		//Phase 2
		List<AutomatingProof> metaproductProofs = loadInKeY(metaproduct);
		proofList = metaproductProofs;
		String metaproductPath = evalPath.getAbsolutePath()+FILE_SEPERATOR+FileManager.finishedProofsDir;
		for(AutomatingProof a : metaproductProofs){
			String defaultName= a.getTypeName()+"__"+a.getTargetName();
			defaultName = defaultName.replace(" ", "");
			File reuse = null;
			AutomatingProof reuseProof = null;
			for(File absProof: abstractProofPart){
				String name = absProof.getName();
				if(name.contains(defaultName)){
					reuse = absProof;
				}
				for(AutomatingProof ap : abstractProofs){
					if(ap.getTargetName().equals(a.getTargetName())&&ap.getTypeName().equals(a.getTypeName())){
						reuseProof = ap;
					}
				}
				if(reuse != null)
					System.out.println(defaultName + ": reuse " + reuse.getName() + " ("+reuse.getAbsolutePath()+")");
				else
					System.out.println(defaultName + ": not reused... no file");
			}
			try {
				a.startMetaProductProof(reuse,DefaultStrategies.defaultSettingsForMetaproduct(),maxRuleApplication,metaproductPath);
				if(!a.isClosed()){
					a.removeProof();
					a.startAbstractProof(maxRuleApplication, DefaultStrategies.defaultSettingsForFeatureStub());
					File restartProof = a.saveProof(savePartialProofsPath);
					a.startMetaProductProof(restartProof,DefaultStrategies.defaultSettingsForMetaproduct(),maxRuleApplication,metaproductPath);
				}
				a.saveProof(metaproductPath);
				AutomatingProof aTotal = new AutomatingProof(a.getTypeName(),
						a.getTargetName(),a.getStat().getNodes(),a.getStat().getBranches(),
						a.getStat().getAppliedRules(),a.getStat().getAutomodeTime(),
						a.getReusedStat().getNodes(),a.getReusedStat().getBranches(),
						a.getReusedStat().getAppliedRules(),a.getReusedStat().getAutomodeTime(),a.isClosed());
				if(reuseProof!=null){
					aTotal.getStat().addStatistics(reuseProof.getStat());
					aTotal.getReusedStat().addStatistics(reuseProof.getReusedStat());
				}
				proofListWithPhase1And2.add(aTotal);
				
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
	}
	
	/**
	 * Performs the evaluation of approach 3 Concrete Contracts
	 * @param loc
	 */
	public void performVa3(File loc, File evalPath){
		String savePath = evalPath.getAbsolutePath()+FILE_SEPERATOR+FileManager.finishedProofsDir;
		proofList = loadInKeY(FileManager.getFirstMetaproductElement(loc));
		boolean firstVersion = loc.getName().contains("1");
		fullProofReuse(evalPath,proofList,DefaultStrategies.defaultSettingsForMetaproduct(),firstVersion,savePath);
	}
	
	/**
	 * Performs the evaluation of approach 4 Method Inlining
	 * @param loc
	 */
	public void performVa4(File loc, File evalPath){
		String savePath = evalPath.getAbsolutePath()+FILE_SEPERATOR+FileManager.finishedProofsDir;
		proofList = loadInKeY(FileManager.getFirstMetaproductElement(loc));
		boolean firstVersion = loc.getName().contains("1");
		fullProofReuse(evalPath,proofList,DefaultStrategies.defaultSettingsForVA4VA5(),firstVersion,savePath);
	}
	/**
	 * Performs the evaluation of approach 5 Thuem et al
	 * @param loc
	 */
	public void performVa5(File loc, File evalPath){
		proofList = loadInKeY(FileManager.getFirstMetaproductElement(loc));
		String savePath = evalPath.getAbsolutePath()+FILE_SEPERATOR+FileManager.finishedProofsDir;
		for(AutomatingProof aproof: proofList){
			aproof.startMetaProductProof(null, DefaultStrategies.defaultSettingsForVA4VA5(), maxRuleApplication,savePath);
			aproof.saveProof(savePath);
		}
	}
	
	/**
	 * Performs the evaluation of approach 6 Thuem et al with Reuse
	 * @param loc
	 */
	public void performVa6(File loc, File evalPath){
		String savePath = evalPath.getAbsolutePath()+FILE_SEPERATOR+FileManager.finishedProofsDir;
		proofList = loadInKeY(FileManager.getFirstMetaproductElement(loc));
		boolean firstVersion = loc.getName().contains("1");
		fullProofReuse(evalPath,proofList,DefaultStrategies.defaultSettingsForVA4VA5(),firstVersion,savePath);
	}
	
	/**
	 * Performs a Verification where the proofs of the first version are reused for the other versions
	 * @param location : path of the evaluation of the current project 
	 * @param a : list of all proofs of the current project
	 * @param s : used StrategyProperties for the verification
	 * @param firstVersion : true if the current project is the first version in this approach
	 * @param savePath : path where the proofs should be saved
	 */
	private void fullProofReuse(File location, List<AutomatingProof> a, StrategyProperties s, boolean firstVersion, String savePath){
		if(firstVersion){
			for(AutomatingProof aproof: a){
				aproof.startMetaProductProof(null, s, maxRuleApplication,savePath);
				aproof.saveProof(savePath);
			}
		}
		else{
			for(AutomatingProof aproof: a){
				aproof.startMetaProductProof(reuseFullProof(location,aproof), s, maxRuleApplication,savePath);
				aproof.saveProof(savePath);
			}
		}
	}
	
	/**
	 * Returns the needed proof file for full proof reuse
	 * @param location has to be evalPath
	 * @param a
	 * @return
	 */
	private File reuseFullProof(File location, AutomatingProof a){
		try{
			File projectv1 = FileManager.getProjectv1Path(location);
			File reuseProofDir = new File (projectv1.getAbsolutePath()+FILE_SEPERATOR+FileManager.finishedProofsDir);
			if(!reuseProofDir.exists()){
				return null;
			}
			File[] reuseProofs = reuseProofDir.listFiles();
			for(File p : reuseProofs){
				String filename = p.getName();
				String defaultName = a.getTypeName()+"__"+a.getTargetName().replace(" ", "");
				if(filename.contains(defaultName)){
					return p;
				}
			}
			return null;	
		}catch(NullPointerException n){
			return null;
		}
	}
	
	private void performFeaturestubVerification(File projectDir, File evalPath, boolean firstVersion){
		performFeaturestubVerification(projectDir,evalPath,firstVersion, false);
	}
	/**
	 * Performs the featurestub phase of the verification
	 * @param projectDir
	 */
	private void performFeaturestubVerification(File projectDir, File evalPath, boolean firstVersion, boolean stubReplay){
		List<File> featurestubs = FileManager.getAllFeatureStubFilesOfAProject(projectDir);
		String currentFeatureStub;
		String saveFeatureStubPath;
		for(File f: featurestubs){
			String[] seperatedPath = f.getAbsolutePath().split("\\"+FILE_SEPERATOR);
			currentFeatureStub = seperatedPath[seperatedPath.length-2];
			saveFeatureStubPath = evalPath.getAbsolutePath()+FILE_SEPERATOR+FileManager.savedProofsDir+FILE_SEPERATOR+currentFeatureStub;
			FileManager.createDir(new File (saveFeatureStubPath));
			List<AutomatingProof> ap = loadInKeY(f);
			phase1ProofList.addAll(ap);
			for(AutomatingProof a : ap){
				//Replay feature stub proof
				if(firstVersion||!proofAlreadyExists(a,evalPath,f.getParentFile())){
					File oldPartialProof = getOldFeatureStubProof(a, FileManager.getProjectv1Path(projectDir));
					if(!firstVersion && stubReplay && oldPartialProof != null) {
						a.replayFeatureStubProof(oldPartialProof, saveFeatureStubPath, maxRuleApplication, DefaultStrategies.defaultSettingsForFeatureStub());
						a.saveProof(saveFeatureStubPath);
						a.setFeaturestub(f.getParentFile().getName());
					} else {
						try {
							a.startAbstractProof(maxRuleApplication, DefaultStrategies.defaultSettingsForFeatureStub());
							a.saveProof(saveFeatureStubPath);
							a.setFeaturestub(f.getParentFile().getName());
						} catch (Exception e) {
							e.printStackTrace();
						}
					}
				}
			}
		}
	}
	
	/**
	 * Checks if the proof was already copied from a previous version
	 * @param a
	 * @param evalPath
	 * @param featurestub
	 * @return
	 */
	private static boolean proofAlreadyExists(AutomatingProof a, File evalPath, File featurestub){
		File savedProofsPath = new File(evalPath+FILE_SEPERATOR+FileManager.savedProofsDir+FILE_SEPERATOR+featurestub.getName());
		File[] proofs = savedProofsPath.listFiles();
		String defaultName= a.getTypeName()+"__"+a.getTargetName().replace(" ", "");
		if(proofs!=null){
			for(File f : proofs){
				if(!f.isDirectory()){
					if(f.getName().endsWith(".proof") && f.getName().contains(defaultName)){
						return true;
					}
				}
			}
		}
		return false;
	}
	
	private static File proofAlreadyExistsAbstract(AutomatingProof a, File evalPath){
		File savedProofsPath = new File(evalPath+FILE_SEPERATOR+FileManager.partialProofsDir);
		File[] proofs = savedProofsPath.listFiles();
		String defaultName= a.getTypeName()+"__"+a.getTargetName().replace(" ", "");
		if(proofs!=null){
			for(File f : proofs){
				if(!f.isDirectory()){
					if(f.getName().endsWith(".proof") && f.getName().contains(defaultName)){
						return f;
					}
				}
			}
		}
		return null;
	}
	
	private static File getOldFeatureStubProof(AutomatingProof a, File toEvaluate){
		File savedProofsPath = new File(toEvaluate+FILE_SEPERATOR+FileManager.partialProofsDir);
		File[] proofs = savedProofsPath.listFiles();
		String defaultName= a.getTypeName()+"__"+a.getTargetName().replace(" ", "");
		if(proofs!=null){
			for(File f : proofs){
				if(!f.isDirectory()){
					if(f.getName().endsWith(".proof") && f.getName().contains(defaultName)){
						return f;
					}
				}
			}
		}
		return null;
	}
	
	public static void sandboxV2() {
		//File ba1stubs = new File("C:\\Users\\User\\Desktop\\Sync\\phd\\ResearchProjects\\2018\\Fefalution\\Evaluation2019\\attempt4\\Evaluation\\test\\1\\BankAccountv1"+FILE_SEPERATOR+featureStubDir);
		//File ba2stubs = new File("C:\\Users\\User\\Desktop\\Sync\\phd\\ResearchProjects\\2018\\Fefalution\\Evaluation2019\\attempt4\\Evaluation\\test\\1\\BankAccountv2"+FILE_SEPERATOR+featureStubDir);
		//List<File> featurestubs = getAllPartialProofs(projectDir,evalPath);
		
		//File partialProofTransactionTransfer = new File("C:\\Users\\User\\Desktop\\Sync\\phd\\ResearchProjects\\2018\\Fefalution\\Evaluation2019\\attempt4\\Evaluation\\test\\1\\BankAccountv1\\Partial Proofs for Metaproduct\\Transaction\\Transaction_transfer.proof");
		//File projectBA1 = new File("C:\\Users\\User\\Desktop\\Sync\\phd\\ResearchProjects\\2018\\Fefalution\\Evaluation2019\\attempt4\\Evaluation\\test\\1\\BankAccountv1");
		
//		File partialProofTransactionTransfer = new File("C:\\Users\\User\\Desktop\\Sync\\phd\\ResearchProjects\\2018\\Fefalution\\Evaluation2019\\attempt4\\Evaluation\\2019-11-27 09-53-48\\VA2 (Metaproduct)\\BankAccountv1\\Partial Proofs for Metaproduct\\Transaction(Transaction__transfer(Account,Account,int)).JML normal_behavior operation contract.0.proof");
//		File projectBA1 = new File("C:\\Users\\User\\Desktop\\Sync\\phd\\ResearchProjects\\2018\\Fefalution\\Evaluation2019\\attempt4\\Evaluation\\2019-11-27 09-53-48\\VA2 (Metaproduct)\\BankAccountv1");

		File partialProofTransactionTransfer = new File("C:\\Users\\User\\Desktop\\Sync\\phd\\ResearchProjects\\2018\\Fefalution\\Evaluation2019\\attempt4\\Evaluation\\v2test\\2\\BankAccountv1\\Partial Proofs for Metaproduct\\Transaction(Transaction__transfer(Account,Account,int)).JML normal_behavior operation contract.0.proof");
		File projectBA1 = new File("C:\\Users\\User\\Desktop\\Sync\\phd\\ResearchProjects\\2018\\Fefalution\\Evaluation2019\\attempt4\\Evaluation\\v2test\\2\\BankAccountv1");
		
		File loc = new File("C:\\Users\\User\\Desktop\\Sync\\phd\\ResearchProjects\\2018\\Fefalution\\Evaluation2019\\attempt4\\BankAccountv1");
		String savePartialProofsPath = projectBA1.getAbsolutePath()+FILE_SEPERATOR+FileManager.partialProofsDir;		
		File java = getMetaproduct(loc);	
		List<AutomatingProof> ap = loadInKeY(java);
		
		String finishedProofPath = projectBA1.getAbsolutePath()+FILE_SEPERATOR+FileManager.finishedProofsDir;
		
		for(AutomatingProof a : ap){
			if(!a.getTargetName().startsWith("transfer")) {
				continue;
			}
			
			//Set<Thread> threadsBefore;	
			a.startMetaProductProof(partialProofTransactionTransfer,DefaultStrategies.defaultSettingsForMetaproduct(),Configuration.maxRuleApplication,finishedProofPath);
			if(!a.isClosed()){
				a.removeProof();
				try {
					a.startAbstractProof(Configuration.maxRuleApplication, DefaultStrategies.defaultSettingsForFeatureStub());
				} catch (Exception e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				File restartProof = a.saveProof(savePartialProofsPath);
				a.startMetaProductProof(restartProof,DefaultStrategies.defaultSettingsForMetaproduct(),Configuration.maxRuleApplication,finishedProofPath);
			}
			//threadsBefore =Thread.getAllStackTraces().keySet();
			a.saveProof(finishedProofPath);
			//a.waitForNewThread(threadsBefore);
			
			System.out.println(a.getTypeName() + " - " + a.getTargetName());
			System.out.println(a.getProof().statistics().nodes);
		}
	}
	
	public static void main(String[] args) {
		//File ba1stubs = new File("C:\\Users\\User\\Desktop\\Sync\\phd\\ResearchProjects\\2018\\Fefalution\\Evaluation2019\\attempt4\\Evaluation\\test\\1\\BankAccountv1"+FILE_SEPERATOR+featureStubDir);
		//File ba2stubs = new File("C:\\Users\\User\\Desktop\\Sync\\phd\\ResearchProjects\\2018\\Fefalution\\Evaluation2019\\attempt4\\Evaluation\\test\\1\\BankAccountv2"+FILE_SEPERATOR+featureStubDir);
		//List<File> featurestubs = getAllPartialProofs(projectDir,evalPath);
		
		File partialProofTransactionTransfer = new File("C:\\Users\\User\\Desktop\\Sync\\phd\\ResearchProjects\\2018\\Fefalution\\Evaluation2019\\attempt4\\Evaluation\\2020-01-16 16-22-28\\1\\BankAccountv1\\Partial Proofs for Metaproduct\\Interest\\Application_nextYear_Interest.proof");
		File projectBA1 = new File("C:\\Users\\User\\Desktop\\Sync\\phd\\ResearchProjects\\2018\\Fefalution\\Evaluation2019\\attempt4\\Evaluation\\2020-01-16 16-22-28\\1\\BankAccountv1");
		
//		File partialProofTransactionTransfer = new File("C:\\Users\\User\\Desktop\\Sync\\phd\\ResearchProjects\\2018\\Fefalution\\Evaluation2019\\attempt4\\Evaluation\\2019-11-27 09-53-48\\VA2 (Metaproduct)\\BankAccountv1\\Partial Proofs for Metaproduct\\Transaction(Transaction__transfer(Account,Account,int)).JML normal_behavior operation contract.0.proof");
//		File projectBA1 = new File("C:\\Users\\User\\Desktop\\Sync\\phd\\ResearchProjects\\2018\\Fefalution\\Evaluation2019\\attempt4\\Evaluation\\2019-11-27 09-53-48\\VA2 (Metaproduct)\\BankAccountv1");

		//File partialProofTransactionTransfer = new File("C:\\Users\\User\\Desktop\\Sync\\phd\\ResearchProjects\\2018\\Fefalution\\Evaluation2019\\attempt4\\Evaluation\\v2test\\2\\BankAccountv1\\Partial Proofs for Metaproduct\\Transaction(Transaction__transfer(Account,Account,int)).JML normal_behavior operation contract.0.proof");
		//File projectBA1 = new File("C:\\Users\\User\\Desktop\\Sync\\phd\\ResearchProjects\\2018\\Fefalution\\Evaluation2019\\attempt4\\Evaluation\\v2test\\2\\BankAccountv1");
		
		//File loc = new File("C:\\Users\\User\\Desktop\\Sync\\phd\\ResearchProjects\\2018\\Fefalution\\Evaluation2019\\attempt4\\BankAccountv1");
		String savePartialProofsPath = projectBA1.getAbsolutePath()+FILE_SEPERATOR+FileManager.partialProofsDir;		
//		
//		
//		
//		
//		//Phase 1
//		File metaproduct = getMetaproduct(loc);
//		List<AutomatingProof> abstractProofs = loadInKeY(metaproduct);
//		phase1ProofList.addAll(abstractProofs);
//		List<File> abstractProofPart = new LinkedList<File>();
//		for(AutomatingProof a : abstractProofs){
//			try {
//				File reuseProof = null;
//				if(!firstVersion){
//					reuseProof = proofAlreadyExistsAbstract(a,evalPath);
//				}
//				if(reuseProof!=null){
//					abstractProofPart.add(reuseProof);
//				}
//				else{
//					a.startAbstractProof(maxRuleApplication, DefaultStrategies.defaultSettingsForFeatureStub());
//					abstractProofPart.add(a.saveProof(savePartialProofsPath));
//				}
//			} catch (Exception e) {
//				e.printStackTrace();
//			}
//		}
		
		//Phase 1
//		File partialProofTransactionTransfer = null;
//		File metaproduct = getMetaproduct(loc);
//		List<AutomatingProof> abstractProofs = loadInKeY(metaproduct);
//		for(AutomatingProof a : abstractProofs){
//			if(!a.getTargetName().startsWith("transfer")) {
//				continue;
//			}
//			try {
//				a.startAbstractProof(Configuration.maxRuleApplication, DefaultStrategies.defaultSettingsForFeatureStub());
//			} catch (Exception e) {
//				// TODO Auto-generated catch block
//				e.printStackTrace();
//			}
//			partialProofTransactionTransfer = a.saveProof(savePartialProofsPath);
//		}
		
		//Phase 2
		File java = getMetaproduct(projectBA1);	
		List<AutomatingProof> ap = loadInKeY(java);
		
		String finishedProofPath = projectBA1.getAbsolutePath()+FILE_SEPERATOR+FileManager.finishedProofsDir;
		
		for(AutomatingProof a : ap){
			if(!a.getTargetName().startsWith("nextYear_Interest")) {
				continue;
			}
			
			Set<Thread> threadsBefore;	
			a.startMetaProductProof(partialProofTransactionTransfer,DefaultStrategies.defaultSettingsForMetaproduct(),Configuration.maxRuleApplication,finishedProofPath);
			if(!a.isClosed()){
				a.removeProof();
				try {
					a.startAbstractProof(Configuration.maxRuleApplication, DefaultStrategies.defaultSettingsForFeatureStub());
				} catch (Exception e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				File restartProof = a.saveProof(savePartialProofsPath);
				a.startMetaProductProof(restartProof,DefaultStrategies.defaultSettingsForMetaproduct(),Configuration.maxRuleApplication,finishedProofPath);
			}
			threadsBefore =Thread.getAllStackTraces().keySet();
			a.saveProof(finishedProofPath);
			a.waitForNewThread(threadsBefore);
			
			System.out.println(a.getTypeName() + " - " + a.getTargetName());
			System.out.println(a.getProof().statistics().nodes);
		}
	}
	
	/**
	 * Performs the second phase of the verification
	 * @param projectDir
	 */
	private void performMetaproductVerification(File projectDir, File evalPath){
		List<File> featurestubs = getAllPartialProofs(projectDir,evalPath);
		File java = getMetaproduct(projectDir);	
		List<AutomatingProof> ap = loadInKeY(java);
		proofList = ap;
		String metaproductPath = evalPath.getAbsolutePath()+FILE_SEPERATOR+FileManager.finishedProofsDir;
		for(AutomatingProof a : ap){
			try {
				Set<Thread> threadsBefore;
				File reuse = getFeatureStubProof(a,featurestubs);
				a.startMetaProductProof(reuse,DefaultStrategies.defaultSettingsForMetaproduct(),maxRuleApplication,metaproductPath);
				threadsBefore =Thread.getAllStackTraces().keySet();
				a.saveProof(metaproductPath);
				a.waitForNewThread(threadsBefore);
				AutomatingProof reusedProof = null;
				for(AutomatingProof firstPhase: phase1ProofList){
					String savename = getSaveName(firstPhase,projectDir);
					if(reuse == null)
						System.out.println("Savename in method meta: " + savename);
					if(reuse.getName().equals(savename)){
						reusedProof = firstPhase;
					}
				}
				AutomatingProof aTotal = new AutomatingProof(a.getTypeName(),
						a.getTargetName(),a.getStat().getNodes(),a.getStat().getBranches(),
						a.getStat().getAppliedRules(),a.getStat().getAutomodeTime(),
						a.getReusedStat().getNodes(),a.getReusedStat().getBranches(),
						a.getReusedStat().getAppliedRules(),a.getReusedStat().getAutomodeTime(),a.isClosed());
				if(reusedProof!=null){
					aTotal.getStat().addStatistics(reusedProof.getStat());
					aTotal.getReusedStat().addStatistics(reusedProof.getReusedStat());
				}
				proofListWithPhase1And2.add(aTotal);
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
	}
	
	public static String getSaveName(AutomatingProof proof,File projectDir){
		String methodname = proof.getTargetName();
		methodname = methodname.replaceAll("\\(.*\\)", "");
		File featurestubFile = new File (projectDir.getAbsolutePath()+FILE_SEPERATOR+FileManager.featureStubDir+FILE_SEPERATOR+proof.getTypeName()+".java");
		File metaproduct = new File(projectDir.getAbsolutePath()+FILE_SEPERATOR+FileManager.metaproductDir+FILE_SEPERATOR+proof.getTypeName()+".java");
		if(MetaProductBuilder.checkForOriginal(featurestubFile,proof.getFeaturestub())||MetaProductBuilder.checkForMethod(methodname+"_"+proof.getFeaturestub(),metaproduct)){
			return proof.getTypeName()+"_"+methodname+"_"+proof.getFeaturestub()+".proof";
		}
		else{
			return proof.getTypeName()+"_"+methodname+".proof";
		}
	}
	
	/**
	 * Returns the first java file of the Metaproduct
	 * @param projectDir
	 * @return
	 */
	private static File getMetaproduct(File projectDir){
		File[] metaproduct = (new File(projectDir.getAbsolutePath()+FILE_SEPERATOR+FileManager.metaproductDir)).listFiles();
		for(File m :metaproduct){
			if(m.getName().endsWith(".java")){
				return m;
			}
		}
		return null;
	}
	
	/**
	 * Returns the proof that should be reused in the second phase of verification for proof ap 
	 * @param ap
	 * @param featureStubProofs
	 * @return
	 */
	private static File getFeatureStubProof(AutomatingProof ap, List<File> featureStubProofs){
		List<File> fittingProofs = new LinkedList<File>();
		for(File proof: featureStubProofs){
			if(isProofForMethod(ap,proof)){
				fittingProofs.add(proof);
			}
		}
		File biggestFile= null;
		for(File f: fittingProofs){
			if(biggestFile == null || f.length()>biggestFile.length()){
				biggestFile = f;
			}
		}
		if(biggestFile == null) {
			System.out.println("Biggestfile is null! Target name was: " + ap.getTargetName() + "; Type name was: " + ap.getTypeName());
			System.out.println("Possible proof files: ");
			featureStubProofs.stream().forEach(f -> System.out.println("    -" + f.getName()));
		}
		return biggestFile;
	}
	
	/**
	 * Returns true, if the given File proof could be reused for the proof ap
	 * @param ap
	 * @param proof
	 * @return
	 */
	private static boolean isProofForMethod(AutomatingProof ap, File proof){
		String method = ap.getTargetName();
		if(method.contains("inv")){
			method = method.replaceAll("<inv>", "inv");
		}
		else{
			method = method.replaceAll("\\(.*\\)", "");
		}
		String predictedName = ap.getTypeName()+"_"+method+".proof";
		if(proof.getName().equals(predictedName)){
				return true;
		}
		return false;
	}
	
	/**
	 * Returns a Filelist with all performed Featurestub proofs 
	 * @param projectDir
	 * @return
	 */
	private static List<File> getAllPartialProofs(File projectDir, File evalPath){
		File featurestub = new File(evalPath.getAbsolutePath()+FILE_SEPERATOR+FileManager.partialProofsDir);
		File[] featurestubs = featurestub.listFiles();
		List<File> proofs = new LinkedList<File>();
		for(File f : featurestubs){
			if(f.isDirectory()){
				File[] fproof = f.listFiles();
				for(File p : fproof){
					if(p.getName().endsWith(".proof")){
						proofs.add(p);
					}
				}
			}
		}
		return proofs;
	}
	/**
	 * 
	 */
	public void warmUp(File location){
		if(Configuration.warmUp){
			AutomatingProof account = getAccountConstructor(location);
			if(account!=null){
				account.startMetaProductProof(null, DefaultStrategies.defaultSettingsForVA4VA5(), maxRuleApplication, null);
				account.removeProof();
			}
		}
	}
	
	public AutomatingProof getAccountConstructor(File location){
		List<AutomatingProof> proofs = loadInKeY(location);
		for(AutomatingProof ap: proofs){
			if(ap.getTypeName().contains("Account")&&ap.getTargetName().contains("Account")){
				return ap;
			}
		}
		return null;
	}

	/**
	 * Loads the selected File location in KeY and returns the list of AutomatingProofs
	 * @param location
	 * @return
	 */
	public static List<AutomatingProof> loadInKeY(File location){
		KeYEnvironment<?> environment;
		environment = KeYEnvironment.loadInMainWindow(location, null, null, true);
		HashMap<String,String> choices =  ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getDefaultChoices();
        choices.put("assertions", "assertions:safe");
        ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().setDefaultChoices(choices);;
		boolean skipLibraryClasses = true;
		Set<KeYJavaType> kjts = environment.getJavaInfo().getAllKeYJavaTypes();
		final Iterator<KeYJavaType> it = kjts.iterator();
        while (it.hasNext()) {
           KeYJavaType kjt = it.next();
           if (!(kjt.getJavaType() instanceof ClassDeclaration || 
                 kjt.getJavaType() instanceof InterfaceDeclaration) || 
               (((TypeDeclaration)kjt.getJavaType()).isLibraryClass() && skipLibraryClasses)) {
              it.remove();
           }
        }
        final KeYJavaType[] kjtsarr = kjts.toArray(new KeYJavaType[kjts.size()]);
        Arrays.sort(kjtsarr, new Comparator<KeYJavaType>() {
            public int compare(KeYJavaType o1, KeYJavaType o2) {
               return o1.getFullName().compareTo(o2.getFullName());
            }
         });
        List<AutomatingProof> proofs = new LinkedList<AutomatingProof>();
        for (KeYJavaType type : kjtsarr) {
            ImmutableSet<IObserverFunction> targets = environment.getSpecificationRepository().getContractTargets(type);
            for (IObserverFunction target : targets) {
                ImmutableSet<Contract> contracts = environment.getSpecificationRepository().getContracts(type, target);
                for (Contract contract : contracts) {
                	if(!type.getFullName().equals(Configuration.excludedClass)||!Configuration.excludeMain){
                		AutomatingProof a =new AutomatingProof(type.getFullName(), ClassTree.getDisplayName(environment.getServices(), contract.getTarget()), contract.getDisplayName(), environment, contract);
                		if(!a.getTargetName().contains("dispatch")||Configuration.proveDispatcher){
                			if(!a.getTargetName().contains("_original_")||Configuration.proveOriginal){
                				proofs.add(a);
                			}
                			if(!Configuration.proveDispatcher&&Configuration.currentMetaproductwithDispatcher){
                				removeDispatcher(proofs);
                			}
                		}
                	}
                }
            }
        }
        return proofs;
        
	}

	private static void removeDispatcher(List<AutomatingProof> proofs){
		//pattern nameMethode_ contains
		List<AutomatingProof> removeDispatcher = new LinkedList<AutomatingProof>();
		for(AutomatingProof a: proofs){
			for(AutomatingProof b: proofs){
				String aNameWithoutBrackets = a.getTargetName().replaceAll("\\(.*\\)", "");
				if(b.getTypeName().equals(a.getTypeName())&&a!=b){
					if(b.getTargetName().contains(aNameWithoutBrackets+"_")){
						removeDispatcher.add(a);
					}
				}
			}
		}
		proofs.removeAll(removeDispatcher);
	}
	

	
	
}
