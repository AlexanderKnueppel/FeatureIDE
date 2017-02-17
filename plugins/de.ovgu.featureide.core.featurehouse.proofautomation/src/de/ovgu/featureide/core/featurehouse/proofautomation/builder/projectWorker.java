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
import java.util.LinkedList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.featurehouse.FeatureHouseComposer;
import de.ovgu.featureide.featurehouse.meta.FeatureStubsGenerator;
import de.ovgu.featureide.fm.ui.handlers.base.SelectionWrapper;

/**
 * Works with the projects in the workspace and generates featurestubs and metaproducts
 * 
 * @author Stefanie
 */
@SuppressWarnings("restriction")
public class projectWorker {
	
	/**
	 * 
	 * @param approachName
	 * @return all projects which belongs to the given approach
	 */
	public static LinkedList<IProject> getProjectsByApproach(String approachName){
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
	
	/**
	 * Generates featurestubs for the given projects
	 * @param projects
	 */
	public static void generateAllFeatureStubsForApproach(LinkedList<IProject> projects){
		for(IProject p: projects){
			try{
				System.out.println(p.toString());
				final IResource res = (IResource) SelectionWrapper.checkClass(p, IResource.class);
				final IFeatureProject featureProject = CorePlugin.getFeatureProject(res);
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
				featureHouseComposer.performFullBuild(config);
				MetaProductBuilder.prepareMetaProduct(new File(f.getBuildPath()));
				p.refreshLocal(IResource.DEPTH_INFINITE, null);
			} catch(Exception e){
				System.out.println("Error building Metaproduct "+p.getName());
				e.printStackTrace();
			}
		}
	}
}
