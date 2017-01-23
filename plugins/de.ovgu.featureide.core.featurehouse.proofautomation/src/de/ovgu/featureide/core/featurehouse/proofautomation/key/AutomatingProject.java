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
import de.ovgu.featureide.core.featurehouse.proofautomation.filemanagement.FileManager;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.ClassTree;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.ExitMainAction;
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
	private static final String FILE_SEPERATOR = System.getProperty("file.separator");
	private List<AutomatingProof> proofList; //contains all proofs of the current project
	private int maxRuleApplication = 10000; // sets the maximal number of rules to be applicated on one proof
	
	public List<AutomatingProof> getProofList(){
		return proofList;
	}
	
	public void setMaxRuleApplication(int mra){
		this.maxRuleApplication = mra;
	}
	
	/**
	 * Performs the evaluation of Phase 1 Fefalution
	 * @param loc
	 */
	public void performVa1(File loc){
		File transactionAccount = new File(loc.getAbsolutePath()+FILE_SEPERATOR+"featurestub"+FILE_SEPERATOR+"Transaction"+FILE_SEPERATOR+"Account.java");
		File lockAccount = new File(loc.getAbsolutePath()+FILE_SEPERATOR+"featurestub"+FILE_SEPERATOR+"Lock"+FILE_SEPERATOR+"Account.java");
		FeatureStubBuilder.prepareForVerification(transactionAccount,lockAccount);
		performFeaturestubVerification(loc);
		FileManager.copySavedProofsToPartialProofs(loc);
		MetaProductBuilder.preparePartialProofs(loc);
		performMetaproductVerification(loc);
	}
	
	/**
	 * Performs the evaluation of Phase 2 Metaproduct
	 * @param loc
	 */
	public void performVa2(File loc){
		File transactionAccount = new File(loc.getAbsolutePath()+FILE_SEPERATOR+"featurestub"+FILE_SEPERATOR+"Transaction"+FILE_SEPERATOR+"Account.java");
		File lockAccount = new File(loc.getAbsolutePath()+FILE_SEPERATOR+"featurestub"+FILE_SEPERATOR+"Lock"+FILE_SEPERATOR+"Account.java");
		FeatureStubBuilder.prepareForVerification(transactionAccount,lockAccount);
	}
	
	/**
	 * Performs the evaluation of Phase 3 Concrete Contracts
	 * @param loc
	 */
	public void performVa3(File loc){
		File transactionAccount = new File(loc.getAbsolutePath()+FILE_SEPERATOR+"featurestub"+FILE_SEPERATOR+"Transaction"+FILE_SEPERATOR+"Account.java");
		File lockAccount = new File(loc.getAbsolutePath()+FILE_SEPERATOR+"featurestub"+FILE_SEPERATOR+"Lock"+FILE_SEPERATOR+"Account.java");
		FeatureStubBuilder.prepareForVerification(transactionAccount,lockAccount);
	}
	
	/**
	 * Performs the evaluation of Phase 4 Method Inlining
	 * @param loc
	 */
	public void performVa4(File loc){
		String metaproductPath = loc.getAbsolutePath()+FILE_SEPERATOR+"Finished Proofs";
		FileManager.createDir(new File (metaproductPath));
		proofList = loadInKeY(new File(loc.getAbsolutePath()+FILE_SEPERATOR+"src"+FILE_SEPERATOR+"Account.java"));
		boolean firstVersion = loc.getName().equals("BankAccountv1");
		fullProofReuse(loc,proofList,DefaultStrategies.defaultSettingsForVA4VA5(),firstVersion,metaproductPath);
		
	}
	
	/**
	 * Performs the evaluation of Phase 5 Thuem et al
	 * @param loc
	 */
	public void performVa5(File loc){
		proofList = loadInKeY(new File(loc.getAbsolutePath()+FILE_SEPERATOR+"src"+FILE_SEPERATOR+"Account.java"));
		String metaproductPath = loc.getAbsolutePath()+FILE_SEPERATOR+"Finished Proofs";
		FileManager.createDir(new File (metaproductPath));
		for(AutomatingProof aproof: proofList){
			aproof.startMetaProductProof(null, DefaultStrategies.defaultSettingsForVA4VA5(), 10000);
			aproof.saveProof(metaproductPath);
		}
	}
	
	/**
	 * Performs a Verification where the proofs of the first version are reused for the other versions
	 * @param location : path of the current project 
	 * @param a : list of all proofs of the current project
	 * @param s : used StrategyProperties for the verification
	 * @param firstVersion : true if the current project is the first version in this phase
	 * @param savePath : path where the proofs should be saved
	 */
	private void fullProofReuse(File location, List<AutomatingProof> a, StrategyProperties s, boolean firstVersion, String savePath){
		if(firstVersion){
			for(AutomatingProof aproof: a){
				aproof.startMetaProductProof(null, s, maxRuleApplication);
				aproof.saveProof(savePath);
			}
		}
		else{
			for(AutomatingProof aproof: a){
				aproof.startMetaProductProof(reuseFullProof(location,aproof), s, maxRuleApplication);
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
		File bankAccountv1 = getBankAccount1Path(location);
		File reuseProofDir = new File (bankAccountv1.getAbsolutePath()+FILE_SEPERATOR+"Finished Proofs");
		if(!reuseProofDir.exists()){
			return null;
		}
		File[] reuseProofs = reuseProofDir.listFiles();
		for(File p : reuseProofs){
			String filename = p.getName();
			String defaultName= a.getTypeName()+"__"+a.getTargetName();
			if(filename.contains(defaultName)){
				System.out.println(filename);
				return p;
			}
		}
		return null;		
	}
	
	/**
	 * Returns the Path of BankAccountv1 of the current Phase
	 * @param location
	 * @return
	 */
	private File getBankAccount1Path(File location){
		String parentPath = location.getParent();
		parentPath = parentPath+FILE_SEPERATOR+"BankAccountv1";
		File parentDir = new File(parentPath);
		if(parentDir.exists()){
			return parentDir;
		}
		else{
			return null;
		}
	}
	
	/**
	 * Performs the featurestub phase of the verification
	 * @param projectDir
	 */
	private void performFeaturestubVerification(File projectDir){
		FileManager.initFolders(projectDir);
		List<File> featurestubs = FileManager.getAllFeatureStubFilesOfAProject(projectDir);
		String currentFeatureStub;
		String saveFeatureStubPath;
		int featurestubIndex = 0;
		for(File f: featurestubs){
			String[] seperatedPath = f.getAbsolutePath().split("\\"+FILE_SEPERATOR);
			currentFeatureStub = seperatedPath[seperatedPath.length-2];
			saveFeatureStubPath = projectDir+FILE_SEPERATOR+"Saved Proofs"+FILE_SEPERATOR+currentFeatureStub;
			FileManager.createDir(new File (saveFeatureStubPath));
			List<AutomatingProof> ap = loadInKeY(f);
			for(AutomatingProof a : ap){
				try {
					a.startFeatureStubProof(10000, DefaultStrategies.defaultSettingsForFeatureStub());
					a.saveProof(saveFeatureStubPath);
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
		}
		MainWindow.getInstance().dispose();
		ExitMainAction exit = new ExitMainAction(MainWindow.getInstance());
		exit.exitMainWithoutInteraction();
	}
	
	/**
	 * Performs the second phase of the verification
	 * @param projectDir
	 */
	private void performMetaproductVerification(File projectDir){
		List<File> featurestubs = getAllFeatureStubProofs(projectDir);
		File java = getMetaproduct(projectDir);	
		List<AutomatingProof> ap = loadInKeY(java);
		proofList = ap;
		String metaproductPath = projectDir+FILE_SEPERATOR+"Finished Proofs";
		for(AutomatingProof a : ap){
			try {
				File reuse = getFeatureStubProof(a,featurestubs);
				a.startMetaProductProof(reuse,null,10000);
				a.saveProof(metaproductPath);
				ProofSettings ps = a.getProof().getSettings();
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		MainWindow.getInstance().dispose();
		ExitMainAction exit = new ExitMainAction(MainWindow.getInstance());
		exit.exitMainWithoutInteraction();
	}
	
	/**
	 * Returns the first java file of the Metaproduct
	 * @param projectDir
	 * @return
	 */
	private static File getMetaproduct(File projectDir){
		File[] metaproduct = (new File(projectDir.getAbsolutePath()+FILE_SEPERATOR+"src")).listFiles();
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
	private static List<File> getAllFeatureStubProofs(File projectDir){
		File featurestub = new File(projectDir.getAbsolutePath()+FILE_SEPERATOR+"Partial Proofs for Metaproduct");
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
                    proofs.add(new AutomatingProof(type.getFullName(), ClassTree.getDisplayName(environment.getServices(), contract.getTarget()), contract.getDisplayName(), environment, contract));
                }
            }
        }
        return proofs;
        
	}

	

	
	
}
