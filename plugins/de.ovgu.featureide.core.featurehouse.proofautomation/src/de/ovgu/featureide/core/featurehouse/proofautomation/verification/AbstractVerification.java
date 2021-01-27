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
package de.ovgu.featureide.core.featurehouse.proofautomation.verification;

import java.io.File;
import java.util.LinkedList;
import java.util.List;
import java.util.regex.Pattern;

import de.ovgu.featureide.core.featurehouse.proofautomation.builder.MetaProductBuilder;
import de.ovgu.featureide.core.featurehouse.proofautomation.configuration.Configuration;
import de.ovgu.featureide.core.featurehouse.proofautomation.filemanagement.FileManager;
import de.ovgu.featureide.core.featurehouse.proofautomation.key.DefaultStrategies;
import de.ovgu.featureide.core.featurehouse.proofautomation.key.KeyHandler;
import de.ovgu.featureide.core.featurehouse.proofautomation.key.ProofHandler;
import de.ovgu.featureide.core.featurehouse.proofautomation.statistics.ProofInformation;

import de.uka.ilkd.key.strategy.StrategyProperties;

/**
 * Abstract Verification is the abstract super Class for all verification methods.
 * 
 * @author marlen
 */
public abstract class AbstractVerification {
	
	public KeyHandler keyHandler = null;
	protected static final String FILE_SEPERATOR = System.getProperty("file.separator");
	String method;
	protected static List<ProofInformation> proofList = new LinkedList<ProofInformation>();;
	protected static List<ProofInformation> phase1ProofList = new LinkedList<ProofInformation>();
	protected static List<ProofInformation> proofListWithPhase1And2= new LinkedList<ProofInformation>();;
	
	private int maxRuleApplication = Configuration.maxRuleApplication; // sets the maximal number of rules to be applicated on one proof

	
	public void performVerification(File loc, File evalPath){};

	/**
	 * 
	 */
	public void warmUp(File location, String method){
		
		this.method = method;
		if(Configuration.warmUp){
			ProofHandler account = getAccountConstructor(location);
			if(account!=null){
				keyHandler.startMetaProductProof(account, location, DefaultStrategies.defaultSettingsForMetaproduct(), maxRuleApplication, null);
				account.removeProof();	
			}
		}
	}
	
	/**
	 * @param loc
	 * @param evalPath
	 * @param firstVersion
	 * @param stubReplay
	 */
	protected void performFeaturestubVerification(File projectDir, File evalPath, boolean firstVersion, boolean stubReplay) {
		List<File> featurestubs = FileManager.getAllFeatureStubFilesOfAProject(projectDir);
		String currentFeatureStub;
		String saveFeatureStubPath;
		
		for(File f: featurestubs){
			String[] seperatedPath = f.getAbsolutePath().split(Pattern.quote(File.separator));
			currentFeatureStub = seperatedPath[seperatedPath.length-2];
			saveFeatureStubPath = evalPath.getAbsolutePath()+FILE_SEPERATOR+FileManager.savedProofsDir+FILE_SEPERATOR+currentFeatureStub;
			FileManager.createDir(new File (saveFeatureStubPath));
			List<ProofHandler> proofHandlers = keyHandler.loadInKeY(f);
			//setphase1ProofList(proofHandlers);
			for(ProofHandler proofHandler : proofHandlers) {
				//Replay feature stub proof
				if(firstVersion||!proofAlreadyExists(proofHandler,evalPath,f.getParentFile())){
					File oldPartialProof = getOldFeatureStubProof(proofHandler, FileManager.getProjectv1Path(projectDir));
					if(!firstVersion && stubReplay && oldPartialProof != null) {
						keyHandler.replayFeatureStubProof(proofHandler,oldPartialProof, saveFeatureStubPath, maxRuleApplication, DefaultStrategies.defaultSettingsForFeatureStub());
						proofHandler.saveProof(saveFeatureStubPath);
						proofHandler.setFeaturestub(f.getParentFile().getName());
					} else {
						try {
							keyHandler.startAbstractProof(proofHandler,maxRuleApplication, DefaultStrategies.defaultSettingsForFeatureStub());
							proofHandler.saveProof(saveFeatureStubPath);
							proofHandler.setFeaturestub(f.getParentFile().getName());
						} catch (Exception e) {
							e.printStackTrace();
						}
					}
				}
			}
			setphase1ProofList(proofHandlers);
		}
	}

	/**
	 * Performs the second phase of the verification used for fefalution
	 * @param projectDir
	 */
	protected void performMetaproductVerification(File projectDir, File evalPath){
		List<File> featurestubs = getAllPartialProofs(projectDir,evalPath);
		File keyFile = getMetaproduct(projectDir);
		List<ProofHandler> proofHandlers = keyHandler.loadInKeY(keyFile);
		//setProofList(proofHandlers); 
		String metaproductPath = evalPath.getAbsolutePath()+FILE_SEPERATOR+FileManager.finishedProofsDir;

		for(ProofHandler proofHandler : proofHandlers){
			try {
				File reuse = getFeatureStubProof(proofHandler,featurestubs);
				keyHandler.startMetaProductProof(proofHandler, reuse, DefaultStrategies.defaultSettingsForMetaproduct(), maxRuleApplication, metaproductPath);
				proofHandler.saveProof(metaproductPath);
				
				ProofInformation reusedProof = null;
				for(ProofInformation firstPhase: phase1ProofList){
					
					String savename = getSaveName(firstPhase,projectDir);
					if(reuse == null)
						System.out.println("Savename in method meta: " + savename);
					if(reuse.getName().equals(savename)){
						reusedProof = firstPhase;
					}
				}
				ProofInformation aTotal = new ProofInformation(proofHandler.getTypeName(),
						proofHandler.getTargetName(),proofHandler.getFeaturestub(),proofHandler.getStat(),proofHandler.getReusedStat(),proofHandler.isClosed());
				if(reusedProof!=null){
					aTotal.getStat().addStatistics(reusedProof.getStat());
					aTotal.getReusedStat().addStatistics(reusedProof.getReusedStat());
				}
				proofHandler.getEnvironment().dispose();
				proofListWithPhase1And2.add(aTotal);
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		setProofList(proofHandlers); 
	}
	/**
	 * 
	 * @return
	 */
	public List<ProofInformation> getProofList(){
		return proofList;
	}
	
	/**
	 * 
	 * @param proofHandlers
	 */
	public void setProofList(List<ProofHandler> proofHandlers) {
		for(ProofHandler p : proofHandlers) {
			ProofInformation proofInformation = new ProofInformation(
					p.getTypeName(), 
					p.getTargetName(),
					p.getFeaturestub(),
					p.getStat(), 
					p.getReusedStat(), 
					p.isClosed());
			proofList.add(proofInformation);
		}
	}
	/**
	 * 
	 * @return phase1ProofList
	 */
	public List<ProofInformation> getPhase1ProofList(){
		return phase1ProofList;
	}
	/**
	 * 
	 * @param proofHandlers
	 */
	public void setphase1ProofList(List<ProofHandler> proofHandlers) {
		for(ProofHandler p : proofHandlers) {
			ProofInformation proofInformation = new ProofInformation(
					p.getTypeName(), 
					p.getTargetName(),
					p.getFeaturestub(),
					p.getStat(), 
					p.getReusedStat(), 
					p.isClosed());
			phase1ProofList.add(proofInformation);
		}
	}
	/**
	 * 
	 * @return proofListWithPhase1And2
	 */
	public List<ProofInformation> getProofListWithPhase1And2(){
		return proofListWithPhase1And2;
	}
	/**
	 * 
	 * @param proofHandlers
	 */
	public void setproofListWithPhase1And2(List<ProofHandler> proofHandlers) {
		for(ProofHandler p : proofHandlers) {
			ProofInformation proofInformation = new ProofInformation(
					p.getTypeName(), 
					p.getTargetName(),
					p.getFeaturestub(),
					p.getStat(), 
					p.getReusedStat(), 
					p.isClosed());
			proofListWithPhase1And2.add(proofInformation);
		}
	}
	/**
	 * 
	 * @param mra
	 */
	public void setMaxRuleApplication(int mra){
		this.maxRuleApplication = mra;
	}
	
	/**
	 * Checks if the proof was already copied from a previous version
	 * @param a
	 * @param evalPath
	 * @param featurestub
	 * @return
	 */
	public boolean proofAlreadyExists(ProofHandler a, File evalPath, File featurestub){
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
	/**
	 * 
	 * @param a
	 * @param evalPath
	 * @return
	 */
	protected File proofAlreadyExistsAbstract(ProofHandler a, File evalPath){
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
	/**
	 * 
	 * @param proofs
	 */
	private static void removeDispatcher(List<ProofHandler> proofs){
		//pattern nameMethode_ contains
		List<ProofHandler> removeDispatcher = new LinkedList<ProofHandler>();
		for(ProofHandler proofInformation: proofs){
			for(ProofHandler proofInformation2: proofs){
				String aNameWithoutBrackets = proofInformation.getTargetName().replaceAll("\\(.*\\)", "");
				if(proofInformation2.getTypeName().equals(proofInformation.getTypeName())&&proofInformation!=proofInformation2){
					if(proofInformation2.getTargetName().contains(aNameWithoutBrackets+"_")){
						removeDispatcher.add(proofInformation);
					}
				}
			}
		}
		proofs.removeAll(removeDispatcher);
	}
	
	
	/**
	 * Returns the proof that should be reused in the second phase of verification for proof ap 
	 * @param proofHandler
	 * @param featureStubProofs
	 * @return
	 */
	protected static File getFeatureStubProof(ProofHandler proofHandler, List<File> featureStubProofs){
		List<File> fittingProofs = new LinkedList<File>();
		for(File proof: featureStubProofs){		
			if(isProofForMethod(proofHandler,proof)){
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
			System.out.println("Biggestfile is null! Target name was: " + proofHandler.getTargetName() + "; Type name was: " + proofHandler.getTypeName());

			System.out.println("Possible proof files: ");
			featureStubProofs.stream().forEach(f -> System.out.println("    -" + f.getName()));
		}
		return biggestFile;
	}
	
	/**
	 * 
	 * @param proof
	 * @param projectDir
	 * @return
	 */
	public static String getSaveName(ProofInformation proof,File projectDir){
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
	 * Returns a Filelist with all performed Featurestub proofs 
	 * @param projectDir
	 * @return
	 */
	protected static List<File> getAllPartialProofs(File projectDir, File evalPath){
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
	 * Returns the first java file of the Metaproduct
	 * @param projectDir
	 * @return
	 */
	protected static File getMetaproduct(File projectDir){
		File[] metaproduct = (new File(projectDir.getAbsolutePath()+FILE_SEPERATOR+FileManager.metaproductDir)).listFiles();
		for(File m :metaproduct){
			//if(m.getName().endsWith(".java")){
			if(m.getName().endsWith(".key")){
				return m;
			}
		}
		return null;
	}
	
	/**
	 * Returns true, if the given File proof could be reused for the proof ap
	 * @param proofHandler
	 * @param proof
	 * @return
	 */
	private static boolean isProofForMethod(ProofHandler proofHandler, File proof){
		String method = proofHandler.getTargetName();
		if(method.contains("inv")){
			method = method.replaceAll("<inv>", "inv");
		}
		else{
			method = method.replaceAll("\\(.*\\)", "");
		}
		String predictedName = proofHandler.getTypeName()+"_"+method+".proof";
		if(proof.getName().equals(predictedName)){
			
				return true;
		}
		return false;
	}
	

	/**
	 * Performs a Verification where the proofs of the first version are reused for the other versions
	 * @param evalPath
	 * @param proofList
	 * @param defaultSettingsForMetaproduct
	 * @param firstVersion
	 * @param savePath
	 */
	public void fullProofReuse(File evalPath, List<ProofHandler> proofList,StrategyProperties s,
			 boolean firstVersion, String savePath, KeyHandler keyHandler) {

		if(firstVersion){
			for(ProofHandler aproof: proofList){
				keyHandler.startMetaProductProof(aproof,null, s, maxRuleApplication,savePath);
				aproof.saveProof(savePath);
			}
		}else{
			for(ProofHandler aproof: proofList){
				keyHandler.startMetaProductProof(aproof,reuseFullProof(evalPath,aproof), s, maxRuleApplication,savePath);
				aproof.saveProof(savePath);
			}
		}
		setProofList(proofList);
		
	}
	/**
	 * @param evalPath
	 * @param aproof
	 * @return
	 */
	protected  File reuseFullProof(File evalPath, ProofHandler aproof) {
		try{
			File projectv1 = FileManager.getProjectv1Path(evalPath);
			File reuseProofDir = new File (projectv1.getAbsolutePath()+FILE_SEPERATOR+FileManager.finishedProofsDir);
			if(!reuseProofDir.exists()){
				return null;
			}
			File[] reuseProofs = reuseProofDir.listFiles();
			for(File p : reuseProofs){
				String filename = p.getName();
				String defaultName = aproof.getTypeName()+"__"+aproof.getTargetName().replace(" ", "");
				if(filename.contains(defaultName)){
					return p;
				}
			}
			return null;	
		}catch(NullPointerException n){
			return null;
		}
	}

	
	/**
	 * Returns the ProofHandler Object from Account 
	 * Only for BankAccount Evaluation
	 * @param location
	 * @return proofHandler
	 */
	public ProofHandler getAccountConstructor(File location){
		List<ProofHandler> proofsHandlers = keyHandler.loadInKeY(location);
		for(ProofHandler proofHandler : proofsHandlers) {
			if(proofHandler.getTypeName().contains("Account") && 
					proofHandler.getTargetName().contains("Account")) {
				return proofHandler;
			}			
		}
		return null;
	}
/**
 * 
 * @param proofHandler
 * @param toEvaluate
 * @return
 */
	private static File getOldFeatureStubProof(ProofHandler proofHandler, File toEvaluate){
		File savedProofsPath = new File(toEvaluate+FILE_SEPERATOR+FileManager.partialProofsDir);
		File[] proofs = savedProofsPath.listFiles();
		String defaultName= proofHandler.getTypeName()+"__"+proofHandler.getTargetName().replace(" ", "");
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
}
