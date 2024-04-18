# Topics of linear algebra covered in the seminar

- Computer algebra systems. Representations of vector and matrices.
- Row operations. Gaussian elimination. Row-reduced echelon form of a matrix.
- Invertible matrices. Elementary matrices. Determinant.
- Linear independence. Bases for the kernel and the image of a linear transformation.
- Rank-nullity theorem and the row space of a matrix. Basis for the row space.
- Change of basis. Coordinates of a vector, matrix of a linear transformation.
- Eigenvalues and the characteristic polynomial. Diagnoalisation.
- The Gram-Schmidt process. Least-square approximation.



## Installation of Sage via conda-forge

SageMath offers a [great installation guide](https://doc.sagemath.org/html/en/installation/) for different OS. SageMath bundles a huge amount of different packages under one umbrella. This can make it a bit tricky to install. Luckily, for macOS and Linux (including WSL, the Windows Subsystem for Linux), we have Conda. [Conda](https://conda.org/) is a multi-platform package management ecosystem. Community-led distributions are available via [conda-forge](https://conda-forge.org/), including SageMath.

So, the only real thing you need is a working conda-forge installation. As [described here](https://doc.sagemath.org/html/en/installation/conda.html), you can install Miniforge, a conda-forge distribution. First, download it:

```bash
curl -L -O "https://github.com/conda-forge/miniforge/releases/latest/download/Miniforge3-$(uname)-$(uname -m).sh"
```

Then, run the script to install it:
```bash
bash Miniforge3-$(uname)-$(uname -m).sh
```

After that, create a new conda environment containing SageMath. (Note that [mamba](https://mamba.readthedocs.io/en/latest/index.html) is a package manager that serves as a faster drop-in replacement for `conda`. It comes pre-installed with Miniforge.)
```
mamba create -n sage sage python=3.11
```

This will download many packages, so it might take a while. It's also very big (it will install ~350 packages corresponding to ~1GB in size). Also feel free to use another Python version if you prefer.

After that, activate the new environment:
```bash
mamba activate sage
```

Now you can run `sage` to access the SageMath REPL that you can interact with in the terminal. But your commands won't get persisted, so a Jupyter Notebook might be a better choice. Read on if you want to use SageMath in Jupyter Notebooks inside VSCode.



### Usage of Sage in Jupyter Notebooks in VSCode

The widespread editor [VSCode](https://code.visualstudio.com/) (Visual Studio Code) has great support for Jupyter notebooks via the [Jupyter extension](https://marketplace.visualstudio.com/items?itemName=ms-toolsai.jupyter) (more than 77 Mio. people have already installed it as of April 2024).

The Jupyter extension itself does _not_ provide a kernel for SageMath, but if you followed along with the installation above, you've already created a working conda environment. VSCode will recognize this and shows you [an option](https://code.visualstudio.com/docs/datascience/jupyter-notebooks#_create-or-open-a-jupyter-notebook) in a Jupyter Notebook to select the SageMath kernel. And that's it, now you can work with SageMath in a Jupyter Notebook locally in VSCode 🎉

If SageMath does not appear in the kernel list, try to restart VSCode (`Ctrl + Shift + P` to open the command palette, then type in "Reload" and click on "Reload Window"). You may also want to refer to [the official guide](https://doc.sagemath.org/html/en/installation/launching.html#using-jupyter-notebook-through-visual-studio-code-vs-code-in-wsl). Rebooting your computer might also help.


#### Tips to get the most out of SageMath in Jupyter Notebooks in VSCode

You might want to add
```py
from sage.all import *
```

at the beginning of the Jupyter notebook. This way, you will get proper IntelliSense including autocompletion. For example, write `ma` and press `Ctrl + Space` and you will see the available options, e.g. `matrix()`. Note that after first importing all modules, it might take a few seconds for IntelliSense to correctly work and recognize your commands.

If a cell outputs LaTeX code, but you rather see something like `\(\displaystyle \left(\begin{array}{rrr}` etc., you can change the cell output presentation to LaTeX by clicking on the three `...`, then `Change Presentation`. LaTeX in markdown cells should work out of the box.


If you prefer to use a JupyterNotebook in the browser, open the terminal (`Ctrl + J` in VSCode), activate sage via `mamba activate sage`, then run `sage -n jupyter`. Your browser will open with a Jupyter Notebook running SageMath and you will see your local files. But this shouldn't have any advantages over the Jupyter Notebook experience in VSCode.
