/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.ui.interfacegen;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.SatSolver;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.CNFType;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;

/**
 * @author Reimar Schröter
 * @author Sebastian Krieter
 */
public class CompositionalAnaylsisTester {

	private final List<String> rootFeatures;
	private final FeatureModel completeModel;
	private final long startTime;

	private long curTime = 0;

	public static void main(final String[] args) throws FileNotFoundException, UnsupportedModelException {
		final CompositionalAnaylsisTester tester = new CompositionalAnaylsisTester(args[0] + "model.xml");
		tester.computeAtomicSets();
	}

	public CompositionalAnaylsisTester(String modelFileName) {
		startTime = System.nanoTime();
		curTime = startTime;
		System.out.print("Reading feature model...");

		completeModel = new FeatureModel();
		try {
			new XmlFeatureModelReader(completeModel).readFromFile(new File(modelFileName));
		} catch (FileNotFoundException | UnsupportedModelException e) {
			CorePlugin.getDefault().logError(e);
			throw new RuntimeException("Could not read feature model from " + modelFileName);
		}

		curTime = split(curTime);
		System.out.print("Computing root features...");
		this.rootFeatures = CorePlugin.splitFeatureModel(completeModel);
		curTime = split(curTime);
	}

	private static long split(long startTime) {
		long curTime = System.nanoTime();
		System.out.println(" -> " + (Math.floor((curTime - startTime) / 1000000.0) / 1000.0) + "s");
		return curTime;
	}

	public void computeAtomicSets() {
		System.out.print("Creating sub models...");

		final List<FeatureModel> subModels = new ArrayList<>();
		final List<Set<String>> unselectedFeatures = new ArrayList<>();
		final List<String> unusedFeatures = createSubModels(subModels, unselectedFeatures, completeModel, rootFeatures);

		final AdvancedNodeCreator nodeCreator = new AdvancedNodeCreator();
		nodeCreator.setCnfType(CNFType.Regular);
		final List<Node> nodeList = new ArrayList<>();
		final List<Node> interfaceNodeList = new ArrayList<>();

		final Iterator<Set<String>> excludedFeaturesIterator = unselectedFeatures.iterator();
		for (FeatureModel subModel : subModels) {
			nodeCreator.setFeatureModel(subModel);
			nodeList.add(nodeCreator.createNodes());
			nodeCreator.setFeatureModel(subModel, excludedFeaturesIterator.next());
			interfaceNodeList.add(nodeCreator.createNodes());
		}

		curTime = split(curTime);
		System.out.print("Removing features (" + unusedFeatures.size() + " / " + completeModel.getNumberOfFeatures() + ")...");

		nodeCreator.setFeatureModel(completeModel);
		nodeList.add(createInterfaceNode(nodeCreator.createNodes(), interfaceNodeList, unusedFeatures));

		curTime = split(curTime);
		System.out.println("Computing atomic sets:");

		final List<List<List<Literal>>> atomicSetLists = new ArrayList<>(nodeList.size());
		int i = nodeList.size();
		for (Node rootNode : nodeList) {
			System.out.print("\t" + i-- + " " + rootNode.getChildren().length);

			final SatSolver solver = new SatSolver(rootNode, 1000, false);
			atomicSetLists.add(solver.atomicSets());

			curTime = split(curTime);
		}

		curTime = split(curTime);
		System.out.print("Merging atomic sets...");

		final List<List<String>> mergeAtomicSets = CorePlugin.mergeAtomicSets(atomicSetLists);

		curTime = split(curTime);
		System.out.println();
		System.out.println(" > Done!");
		System.out.print("Global Time");
		split(startTime);

		System.out.println();
		System.out.println("Result:");
		System.out.println(mergeAtomicSets.size());
		for (List<String> list : mergeAtomicSets) {
			if (list.size() > 1) {
				System.out.println("\t Size = " + list.size());
			}
		}
		System.out.println(mergeAtomicSets);
	}

	private Node createInterfaceNode(Node rootNode, List<Node> interfaceNodes, Collection<String> unusedFeatures) {
		final HashSet<String> unusedFeatureSet = new HashSet<>(unusedFeatures);
		final Node[] clauses = rootNode.getChildren();

		int removeCount = 0;
		for (int i = 0; i < clauses.length; i++) {
			final Node[] literals = clauses[i].getChildren();
			for (int j = 0; j < literals.length; j++) {
				final Literal literal = (Literal) literals[j];
				if (unusedFeatureSet.contains(literal.var)) {
					clauses[i] = null;
					removeCount++;
					break;
				}
			}
		}

		int newLength = clauses.length - removeCount;
		int curIndex = newLength;

		for (Node clause : interfaceNodes) {
			newLength += clause.getChildren().length;
		}

		final Node[] newClauses = new Node[newLength];

		if (removeCount > 0) {
			int j = 0;
			for (int i = 0; i < clauses.length; i++) {
				final Node clause = clauses[i];
				if (clause != null) {
					newClauses[j++] = clause;
				}
			}
		} else {
			System.arraycopy(clauses, 0, newClauses, 0, clauses.length);
		}

		for (Node clause : interfaceNodes) {
			final Node[] children = clause.getChildren();
			System.arraycopy(children, 0, newClauses, curIndex, children.length);
			curIndex += children.length;
		}

		return new And(newClauses);
	}

	private List<String> createSubModels(List<FeatureModel> subModels, List<Set<String>> unselectedFeatures, FeatureModel model, List<String> rootFeatureNames) {
		for (int i = 0; i < rootFeatureNames.size(); i++) {
			final String rootFeatureName = rootFeatureNames.get(i);

			if (model.getFeature(rootFeatureName) == null) {
				for (final Feature feature : model.getFeatures()) {
					if (feature.getName().endsWith(rootFeatureName)) {
						rootFeatureNames.set(i, feature.getName());
						break;
					}
				}
			}
		}

		final List<String> unusedFeatures = new ArrayList<>();

		for (final String rootFeature : rootFeatureNames) {
			final Feature root = model.getFeature(rootFeature);
			if (root == null) {
				throw new RuntimeException("Feature " + rootFeature + " not found!");
			}
			final FeatureModel newSubModel = new FeatureModel(model, root, false);
			final Set<String> includeFeatures = new HashSet<>();
			final Set<String> excludeFeatures = new HashSet<>(newSubModel.getFeatureNames());
			includeFeatures.add(root.getName());

			final HashSet<Constraint> crossModelConstraints = new HashSet<>(model.getConstraints());
			crossModelConstraints.removeAll(newSubModel.getConstraints());
			for (final Constraint constr : crossModelConstraints) {
				for (Feature feature : constr.getContainedFeatures()) {
					includeFeatures.add(feature.getName());
				}
			}
			includeFeatures.retainAll(newSubModel.getFeatureNames());
			excludeFeatures.removeAll(includeFeatures);

			List<String> clone = new ArrayList<>(rootFeatureNames);
			clone.remove(newSubModel.getRoot().getName());

			if (!Collections.disjoint(newSubModel.getFeatureNames(), clone)) {
				throw new RuntimeException("Nested Root " + rootFeature + "!");
			}

			unselectedFeatures.add(excludeFeatures);
			unusedFeatures.addAll(excludeFeatures);
			subModels.add(newSubModel);
		}
		return unusedFeatures;
	}

}
