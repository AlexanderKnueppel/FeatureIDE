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
package de.ovgu.featureide.core.featurehouse.proofautomation.builder;

import java.io.File;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.featurehouse.proofautomation.configuration.Configuration;
import de.ovgu.featureide.core.featurehouse.proofautomation.filemanagement.FileManager;
import de.ovgu.featureide.featurehouse.FeatureHouseComposer;
import de.ovgu.featureide.featurehouse.meta.FeatureStubsGenerator;
import de.ovgu.featureide.featurehouse.meta.FeatureStubsGeneratorNonRigid;
import de.ovgu.featureide.fm.ui.handlers.base.SelectionWrapper;

/**
 * Works with the projects in the workspace and generates featurestubs and metaproducts
 * 
 * @author Stefanie
 */
@SuppressWarnings("restriction")
public class projectWorker2 {
	
	/**
	 * 
	 * @param approachName
	 * @return all projects which belongs to the given approach
	 */
	//todo: adjust to getAllProjects should be independent of approach
	public static LinkedList<IProject> getProjectsByApproach(String approachName){
		System.out.println(approachName);
		IWorkspaceRoot myWorkspaceRoot = ResourcesPlugin.getWorkspace().getRoot();
		IProject[] allProjects = myWorkspaceRoot.getProjects();
		LinkedList<IProject> allProjectsForApproach = new LinkedList<IProject>();
		for(IProject p: allProjects){
			File f = p.getLocation().toFile();
			if(f.getParentFile().getName().equals(approachName)){
				allProjectsForApproach.add(p);
			}
		}
		return allProjectsForApproach;
	}
	
	public static void sandbox() {
		List<String> accounts = new ArrayList<String>();
		File dir = new File("C:\\Users\\User\\Desktop\\Sync\\phd\\ResearchProjects\\2018\\Fefalution\\Evaluation2019\\attempt4\\");
		
		
		
//		generateCodeForSingleProject(dir.getName(), false, true);
		
//		String FILE_SEPERATOR = System.getProperty("file.separator");
//		System.out.println("Name: " + dir.getName());
//		if(dir.getName().contains("5") || dir.getName().contains("6")) {
//			File acc = new File(dir.getAbsolutePath()+FILE_SEPERATOR+FileManager.metaproductDir+FILE_SEPERATOR+"Account.java");
//			BuilderUtil.fixUpdateLoggingInBA5BA6(acc);
//		}
	}
	
	public static void generateFeatureStub(LinkedList<IProject> projects) {
		for(IProject p: projects){
			try{
				final IResource res = (IResource) SelectionWrapper.checkClass(p, IResource.class);
				final IFeatureProject featureProject = CorePlugin.getFeatureProject(res);
				if (featureProject != null) {
					FeatureStubsGeneratorNonRigid fsg = new FeatureStubsGeneratorNonRigid(featureProject);
					fsg.generate();
					while(true){
						Thread.sleep(100); //necessary because of timing problems 
						if(fsg.finished){
							break;
						}
					}
				}
			} catch(Exception e){
				System.out.println("Error building featurestub:");
				e.printStackTrace();
			}
		}
		
	}
	
	public static void generateCodeForSingleProject(String projectName,boolean featurestub,boolean newMetaproduct){
		
		IProject p = getProjectByName(projectName);
		if(p!=null){
			final IFeatureProject featureProject = CorePlugin.getFeatureProject(p);			
			try{
				FeatureHouseComposer featureHouseComposer = (FeatureHouseComposer) featureProject.getComposer();
				featureHouseComposer.setBuildMetaProduct(true);
				IFile config = featureProject.getCurrentConfiguration();
				if(newMetaproduct){
					featureProject.setMetaProductGeneration(IFeatureProject.META_THEOREM_PROVING_DISP);
				}
				else{
					featureProject.setMetaProductGeneration(IFeatureProject.META_THEOREM_PROVING);
				}
				if(Configuration.generateMetaproduct){
					featureHouseComposer.performFullBuild(config);
				}
				MetaProductBuilder.prepareMetaProduct(new File(featureProject.getBuildPath()));
				p.refreshLocal(IResource.DEPTH_INFINITE, null);
			} catch(Exception e){
				System.out.println("Error building Metaproduct "+p.getName());
				e.printStackTrace();
			}
			if(featurestub){
				try{
					if (featureProject != null) {
						FeatureStubsGenerator fsg = new FeatureStubsGenerator(featureProject);
						fsg.generate();
						while(true){
							Thread.sleep(100); //necessary because of timing problems 
							if(fsg.finished){
								break;
							}
						}
					}
				} catch(Exception e){
					System.out.println("Error building featurestub:");
					e.printStackTrace();
				}
			}
			
		}
	}
	
	public static IProject getProjectByName(String name){
		IWorkspaceRoot myWorkspaceRoot = ResourcesPlugin.getWorkspace().getRoot();
		IProject[] allProjects = myWorkspaceRoot.getProjects();
		for(IProject p: allProjects){
			File f = p.getLocation().toFile();
			if(f.getName().equals(name)){
				return p;
			}
		}
		return null;
	}
	
	/**
	 * Generates featurestubs for the given projects
	 * @param projects
	 */
	public static void generateAllFeatureStubsForApproach(LinkedList<IProject> projects){
		for(IProject p: projects){
			try{
				final IResource res = (IResource) SelectionWrapper.checkClass(p, IResource.class);
				
				final IFeatureProject featureProject = CorePlugin.getFeatureProject(res);
				if (featureProject != null) {
					FeatureStubsGeneratorNonRigid fsg = new FeatureStubsGeneratorNonRigid(featureProject);
					fsg.generate();
					while(true){
						Thread.sleep(100); //necessary because of timing problems 
						if(fsg.finished){
							break;
						}
					}
				}
			} catch(Exception e){
				System.out.println("Error building featurestub:");
				e.printStackTrace();
			}
		}
	}
	
	/**
	 * Generates metaproducts for the given projects
	 * @param projects
	 * @param newMetaproduct
	 */
	public static void generateAllMetaproductsForApproach(LinkedList<IProject> projects, boolean newMetaproduct){
		for(IProject p: projects){
			try{
				IFeatureProject f = CorePlugin.getFeatureProject(p);
				FeatureHouseComposer featureHouseComposer = (FeatureHouseComposer) f.getComposer();
				featureHouseComposer.setBuildMetaProduct(true);
				IFile config = f.getCurrentConfiguration();
				if(newMetaproduct){
					f.setMetaProductGeneration(IFeatureProject.META_THEOREM_PROVING_DISP);
				}
				else{
					f.setMetaProductGeneration(IFeatureProject.META_THEOREM_PROVING);
				}
				if(Configuration.generateMetaproduct){
					featureHouseComposer.performFullBuild(config);
				}
				MetaProductBuilder.prepareMetaProduct(new File(f.getBuildPath()));
				p.refreshLocal(IResource.DEPTH_INFINITE, null);
			} catch(Exception e){
				System.out.println("Error building Metaproduct "+p.getName());
				e.printStackTrace();
			}
		}
	}
}
