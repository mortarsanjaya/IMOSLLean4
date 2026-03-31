# IMOSLLean4

Formalization of IMO Shortlist Problems in Lean 4.

This repository stores formalization of IMO Shortlist problems from 2006 onwards in Lean 4.
It mainly covers problems in the Algebra and Number Theory category, with some problems in the Combinatorics category included as well.
All problems formalized here include their complete solutions.

Aside from formalizing the IMO Shortlist problems, this repository also formalizes attempts to generalize a few of these problems.
For example, after rephrasing, the IMO Shortlist 2012 N8 problem reads as follows.

> For any prime power $q$, let $\mathbb{F}_q$ be the finite field of $q$ elements.
Prove that for every prime $p > 100$ and for every $r \in \mathbb{F}_p$, there exist two elements $a, b \in \mathbb{F}_p$ such that $a^2 + b^5 = r$.

Then we prove more:

> For any finite field $F$ of cardinality not equal to $11$ and for every $r \in F$, there exist two elements $a, b \in F$ such that $a^2 + b^5 = r$ (and that this fails for cardinality $11$).

## Installation and Dependencies

Please follow the instructions at https://leanprover-community.github.io/install/project.html about working on an existing project.

This project depends on [Mathlib4](https://github.com/leanprover-community/mathlib4) and is currently using version **4.29.0**.

## Documentation

The documentation of this project is available on [this webpage](https://mortarsanjaya.github.io/IMOSLLean4/).
This documentation is built using [doc-gen4](https://github.com/leanprover/doc-gen4).

The folder `IMOSLLean4/Main` contains the formalization of the IMO Shortlist problems. 
The files here are organized by year.
The formalization of the main statement to be proved is named `final_solution`.
If there are multiple parts to the problem, then part 1 is named `final_solution_part1`, part 2 is named `final_solution_part2`, and so on.

Meanwhile, the folder `IMOSLLean4/Generalization` contains formalization of generalized versions of some IMO Shortlist problems, such as the aforementioned IMO Shortlist 2012 N8 problem.
The files here are organized by the problem they generalize.

## Contributing

Thank you for your interest in contributing to this project!
This repository is a personal project, so currently I am not looking for external contributions.
That being said, feel free to fork this repository for your needs.

## Progress

Below are some statistics on the number of problems formalized in this repository as of **March 17, 2026**.
Here, "A" stands for Algebra, "C" stands for Combinatorics, and "N" stands for Number Theory.

<table align=center>
  <thead>
    <tr>
      <th rowspan=3>Year</th>
      <th colspan=8>Number of problems</th>
    </tr>
    <tr>
      <th colspan=4>Formalized</th>
      <th colspan=4>All</th>
    </tr>
    <tr>
      <th>A</th>
      <th>C</th>
      <th>N</th>
      <th>Total</th>
      <th>A</th>
      <th>C</th>
      <th>N</th>
      <th>Total</th>
    </tr>
  </thead>
  <tbody>
    <tr>
      <td align=center>2006</td>
      <td align=center>4</td>
      <td align=center>0</td>
      <td align=center>6</td>
      <td align=center>10</td>
      <td align=center>6</td>
      <td align=center>7</td>
      <td align=center>7</td>
      <td align=center>20</td>
    </tr>
    <tr>
      <td align=center>2007</td>
      <td align=center>5</td>
      <td align=center>1</td>
      <td align=center>5</td>
      <td align=center>11</td>
      <td align=center>7</td>
      <td align=center>8</td>
      <td align=center>7</td>
      <td align=center>22</td>
    </tr>
    <tr>
      <td align=center>2008</td>
      <td align=center>5</td>
      <td align=center>3</td>
      <td align=center>2</td>
      <td align=center>10</td>
      <td align=center>7</td>
      <td align=center>6</td>
      <td align=center>6</td>
      <td align=center>19</td>
    </tr>
    <tr>
      <td align=center>2009</td>
      <td align=center>7</td>
      <td align=center>4</td>
      <td align=center>6</td>
      <td align=center>17</td>
      <td align=center>7</td>
      <td align=center>8</td>
      <td align=center>7</td>
      <td align=center>22</td>
    </tr>
    <tr>
      <td align=center>2010</td>
      <td align=center>5</td>
      <td align=center>1</td>
      <td align=center>3</td>
      <td align=center>9</td>
      <td align=center>8</td>
      <td align=center>7</td>
      <td align=center>6</td>
      <td align=center>21</td>
    </tr>
    <tr>
      <td align=center>2011</td>
      <td align=center>6</td>
      <td align=center>0</td>
      <td align=center>4</td>
      <td align=center>10</td>
      <td align=center>7</td>
      <td align=center>7</td>
      <td align=center>8</td>
      <td align=center>22</td>
    </tr>
    <tr>
      <td align=center>2012</td>
      <td align=center>4</td>
      <td align=center>2</td>
      <td align=center>5</td>
      <td align=center>11</td>
      <td align=center>7</td>
      <td align=center>7</td>
      <td align=center>8</td>
      <td align=center>22</td>
    </tr>
    <tr>
      <td align=center>2013</td>
      <td align=center>2</td>
      <td align=center>0</td>
      <td align=center>4</td>
      <td align=center>6</td>
      <td align=center>6</td>
      <td align=center>8</td>
      <td align=center>7</td>
      <td align=center>21</td>
    </tr>
    <tr>
      <td align=center>2014</td>
      <td align=center>3</td>
      <td align=center>2</td>
      <td align=center>3</td>
      <td align=center>8</td>
      <td align=center>6</td>
      <td align=center>9</td>
      <td align=center>8</td>
      <td align=center>23</td>
    </tr>
    <tr>
      <td align=center>2015</td>
      <td align=center>3</td>
      <td align=center>0</td>
      <td align=center>4</td>
      <td align=center>7</td>
      <td align=center>6</td>
      <td align=center>7</td>
      <td align=center>8</td>
      <td align=center>21</td>
    </tr>
    <tr>
      <td align=center>2016</td>
      <td align=center>4</td>
      <td align=center>1</td>
      <td align=center>2</td>
      <td align=center>7</td>
      <td align=center>8</td>
      <td align=center>8</td>
      <td align=center>8</td>
      <td align=center>24</td>
    </tr>
    <tr>
      <td align=center>2017</td>
      <td align=center>7</td>
      <td align=center>1</td>
      <td align=center>3</td>
      <td align=center>11</td>
      <td align=center>8</td>
      <td align=center>8</td>
      <td align=center>8</td>
      <td align=center>24</td>
    </tr>
    <tr>
      <td align=center>2018</td>
      <td align=center>1</td>
      <td align=center>1</td>
      <td align=center>4</td>
      <td align=center>6</td>
      <td align=center>7</td>
      <td align=center>7</td>
      <td align=center>7</td>
      <td align=center>21</td>
    </tr>
    <tr>
      <td align=center>2019</td>
      <td align=center>2</td>
      <td align=center>1</td>
      <td align=center>3</td>
      <td align=center>6</td>
      <td align=center>7</td>
      <td align=center>9</td>
      <td align=center>8</td>
      <td align=center>24</td>
    </tr>
    <tr>
      <td align=center>2020</td>
      <td align=center>3</td>
      <td align=center>0</td>
      <td align=center>3</td>
      <td align=center>6</td>
      <td align=center>8</td>
      <td align=center>8</td>
      <td align=center>7</td>
      <td align=center>23</td>
    </tr>
    <tr>
      <td align=center>2021</td>
      <td align=center>6</td>
      <td align=center>2</td>
      <td align=center>2</td>
      <td align=center>10</td>
      <td align=center>8</td>
      <td align=center>8</td>
      <td align=center>8</td>
      <td align=center>24</td>
    </tr>
    <tr>
      <td align=center>2022</td>
      <td align=center>3</td>
      <td align=center>2</td>
      <td align=center>2</td>
      <td align=center>7</td>
      <td align=center>8</td>
      <td align=center>9</td>
      <td align=center>8</td>
      <td align=center>25</td>
    </tr>
    <tr>
      <td align=center>2023</td>
      <td align=center>3</td>
      <td align=center>0</td>
      <td align=center>6</td>
      <td align=center>9</td>
      <td align=center>7</td>
      <td align=center>7</td>
      <td align=center>8</td>
      <td align=center>22</td>
    </tr>
    <tr>
      <td align=center>2024</td>
      <td align=center>2</td>
      <td align=center>1</td>
      <td align=center>4</td>
      <td align=center>7</td>
      <td align=center>8</td>
      <td align=center>8</td>
      <td align=center>7</td>
      <td align=center>23</td>
    </tr>
    <tr>
      <td align=center>Total</td>
      <td align=center>75</td>
      <td align=center>22</td>
      <td align=center>71</td>
      <td align=center>168</td>
      <td align=center>136</td>
      <td align=center>146</td>
      <td align=center>141</td>
      <td align=center>423</td>
    </tr>
  </tbody>
</table>
