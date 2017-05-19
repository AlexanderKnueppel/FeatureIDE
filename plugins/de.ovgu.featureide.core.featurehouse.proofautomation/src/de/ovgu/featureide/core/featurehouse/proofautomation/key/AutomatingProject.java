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
	 * @param phase1ProofList the phase1ProofList to set
	 */
	public void setPhase1ProofList(List<AutomatingProof> phase1ProofList) {
		this.phase1ProofList = phase1ProofList;
	}

	public void setMaxRuleApplication(int mra){
		this.maxRuleApplication = mra;
	}
	
	/**
	 * Performs the evaluation of approach 1 Fefalution
	 * @param loc
	 */
	public void performVa1(File loc, File evalPath){
		File transactionAccount = new File(loc.getAbsolutePath()+FILE_SEPERATOR+FileManager.featureStubDir+FILE_SEPERATOR+"Transaction"+FILE_SEPERATOR+"Account.java");
		File lockAccount = new File(loc.getAbsolutePath()+FILE_SEPERATOR+FileManager.featureStubDir+FILE_SEPERATOR+"Lock"+FILE_SEPERATOR+"Account.java");
		FeatureStubBuilder.prepareForVerification(transactionAccount,lockAccount);
		boolean firstVersion =loc.getName().contains("1");
		if(!firstVersion){
			FileManager.reuseFeaturestub(evalPath, loc);
		}
		performFeaturestubVerification(loc,evalPath,firstVersion);
		FileManager.copySavedProofsToPartialProofs(evalPath);
		MetaProductBuilder.preparePartialProofs(loc,evalPath);
		performMetaproductVerification(loc,evalPath);
	}
	
	/**
	 * Performs the evaluation of approach 2 Metaproduct
	 * @param loc
	 */
	public void performVa2(File loc,File evalPath){
		//Phase 1
		String savePartialProofsPath = evalPath.getAbsolutePath()+FILE_SEPERATOR+FileManager.partialProofsDir;
		File metaproduct = getMetaproduct(loc);
		List<AutomatingProof> abstractProofs = loadInKeY(metaproduct);
		phase1ProofList.addAll(abstractProofs);
		List<File> abstractProofPart = new LinkedList<File>();
		for(AutomatingProof a : abstractProofs){
			try {
				System.out.println(a.getTargetName()+a.getTypeName());
				a.startAbstractProof(maxRuleApplication, DefaultStrategies.defaultSettingsForFeatureStub());
				abstractProofPart.add(a.saveProof(savePartialProofsPath));
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		//Phase 2
		List<AutomatingProof> metaproductProofs = loadInKeY(metaproduct);
		proofList = metaproductProofs;
		String metaproductPath = evalPath.getAbsolutePath()+FILE_SEPERATOR+FileManager.finishedProofsDir;
		for(AutomatingProof a : metaproductProofs){
			String defaultName= a.getTypeName()+"__"+a.getTargetName();
			File reuse = null;
			for(File absProof: abstractProofPart){
				if(absProof.getName().contains(defaultName)){
					reuse = absProof;
				}			
			}
			try {
				a.startMetaProductProof(reuse,DefaultStrategies.defaultSettingsForMetaproduct(),maxRuleApplication,metaproductPath);
				a.saveProof(metaproductPath);
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
		fullProofReuse(loc,proofList,DefaultStrategies.defaultSettingsForMetaproduct(),firstVersion,savePath);
	}
	
	/**
	 * Performs the evaluation of approach 4 Method Inlining
	 * @param loc
	 */
	public void performVa4(File loc, File evalPath){
		String savePath = evalPath.getAbsolutePath()+FILE_SEPERATOR+FileManager.finishedProofsDir;
		proofList = loadInKeY(FileManager.getFirstMetaproductElement(loc));
		boolean firstVersion = loc.getName().contains("1");
		fullProofReuse(loc,proofList,DefaultStrategies.defaultSettingsForVA4VA5(),firstVersion,savePath);
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
		fullProofReuse(loc,proofList,DefaultStrategies.defaultSettingsForVA4VA5(),firstVersion,savePath);
	}
	
	/**
	 * Performs a Verification where the proofs of the first version are reused for the other versions
	 * @param location : path of the current project 
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
	 * @param location
	 * @param a
	 * @return
	 */
	private File reuseFullProof(File location, AutomatingProof a){
		File projectv1 = FileManager.getCurrentEvaluationPath(FileManager.getProjectv1Path(location));
		File reuseProofDir = new File (projectv1.getAbsolutePath()+FILE_SEPERATOR+FileManager.finishedProofsDir);
		if(!reuseProofDir.exists()){
			return null;
		}
		File[] reuseProofs = reuseProofDir.listFiles();
		for(File p : reuseProofs){
			String filename = p.getName();
			String defaultName= a.getTypeName()+"__"+a.getTargetName();
			if(filename.contains(defaultName)){
				return p;
			}
		}
		return null;		
	}
	
	
	/**
	 * Performs the featurestub phase of the verification
	 * @param projectDir
	 */
	private void performFeaturestubVerification(File projectDir, File evalPath, boolean firstVersion){
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
				if(firstVersion||!proofAlreadyExists(a,evalPath,f.getParentFile())){
					try {
						a.startAbstractProof(maxRuleApplication, DefaultStrategies.defaultSettingsForFeatureStub());
						a.saveProof(saveFeatureStubPath);
					} catch (Exception e) {
						e.printStackTrace();
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
		String defaultName= a.getTypeName()+"__"+a.getTargetName();
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
			} catch (Exception e) {
				e.printStackTrace();
			}
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
		AutomatingProof account = getAccountConstructor(location);
		if(account!=null){
			account.startMetaProductProof(null, DefaultStrategies.defaultSettingsForVA4VA5(), maxRuleApplication, null);
			account.getProof().pruneProof(account.getProof().root());
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
                			proofs.add(a);
                		}
                	}
                }
            }
        }
        return proofs;
        
	}

	private void removeDispatcher(List<AutomatingProof> proofs){

	}
	

	
	
}
