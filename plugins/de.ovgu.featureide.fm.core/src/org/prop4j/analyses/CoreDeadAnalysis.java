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
package org.prop4j.analyses;

import java.util.List;

import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.ISatSolver.SelectionStrategy;
import org.prop4j.solver.ISatSolver.Tester;

import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds core and dead features.
 * 
 * @author Sebastian Krieter
 */
public class CoreDeadAnalysis extends AbstractAnalysis<List<String>> {

	public CoreDeadAnalysis(ISatSolver solver) {
		super(solver);
	}

	public class SolutionTester implements Tester {
		@Override
		public int getNextVariable(int index) {
			final int size = solver.getNumberOfSolutions();
			final List<int[]> solutions = solver.getSolutions();
			if (size > 0) {
				final int[] firstSolution = solutions.get(0);
				final int mx = firstSolution[index];
				for (int i = 1; i < size; i++) {
					if ((mx != solutions.get(i)[index])) {
						return 0;
					}
				}
				return -mx;
			}
			return 0;
		}
	}

	public List<String> execute(IMonitor monitor) throws Exception {
		analyze();
		return solver.getAssignmentString();
	}

	public void analyze() throws InterruptedException {
		solver.setSelectionStrategy(SelectionStrategy.POSITIVE);
		int[] model1 = solver.findModel();
		solver.setSelectionStrategy(SelectionStrategy.NEGATIVE);
		int[] model2 = solver.findModel();

		if (model1 != null) {
			// if there are more negative than positive literals
			if (model1.length - countNegative(model1) < countNegative(model2)) {
				solver.setSelectionStrategy(SelectionStrategy.POSITIVE);
			}

			solver.checkAllVariables(model1.length, new SolutionTester());
		}
	}

	private static int countNegative(int[] model) {
		int count = 0;
		for (int i = 0; i < model.length; i++) {
			count += model[i] >>> (Integer.SIZE - 1);
		}
		return count;
	}

}
