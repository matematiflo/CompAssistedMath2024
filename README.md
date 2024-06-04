<div align="center">
  <h3 align="center">Computer-assisted mathematics 2024</h3>
  <p>
    <strong>GitHub repository for the seminar on Computer-assisted mathematics
      <br>held at the University of Heidelberg during the Summer Semester of 2024.</strong>
  </p>
</div>

<div align="center">
  <a href="https://matematiflo.github.io/SoSe_2024/CompAssistedMath2024">Homepage</a>
  | <a href="https://matematiflo.zulipchat.com/join/xju6njq6imfu44qk4rfbg5hg/">Zulip</a>
  | <a href="https://doc.sagemath.org/html/en/index.html">Sage Docs</a>
  | <a href="./Sage/README.md#installation-of-sage-via-conda-forge">Sage Installation guide</a>
</div>

## Set up the repo

### Install Lean

1. Install [elan](https://github.com/leanprover/elan), the Lean version manager (follow the installation instructions on the linked GitHub repository).
1. Install Lean's current stable version using the following command in a terminal window.

```script
elan toolchain install stable
```

This will download and intall Lean on your computer. You can check that Lean has been installed using the following command.

```script
elan toolchain list
```

As part of this installation, you should have `lake` (Lean's package manager) installed on your machine. You can check this using the following command.

```script
lake --version
```

If this does not work, try closing and reopening your terminal window.

### Troubleshooting

In case of trouble, check out the installation instructions:

- In the official [Lean manual](https://lean-lang.org/lean4/doc/setup.html).
- On the [leanprover-community](https://leanprover-community.github.io/get_started.html) website.

### Clone the repo

Either clone this repo using GitHub Desktop or, in a terminal window, go to the folder where you would like to clone it and run the following command:

```script
git clone https://github.com/matematiflo/CompAssistedMath2024.git
```

This repo uses the mathematical libray [Mathlib](https://github.com/leanprover-community/mathlib4), so you will need to update your Lean version to the one used by Mathlib at the time you are cloning the repo. You can do so by following the instructions below.

### Update your Lean version and download the compiled Mathlib files

Go to the folder where you have cloned the repo and run the following commands.

The first one updates the Lean version used in your repo to match Mathlib's current version (the `lean-toolchain` file will be modified).

```script
curl https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain
```

The second command updates your Lean installation and adds a Mathlib dependency.

```script
lake update
```

The final (optional) command downloads Mathlib's pre-compiled files, so you do not have to compile them when you need to import them.

```script
lake exe cache get
```

If this does not work, you can always try to open the current repo in a Codespace!
