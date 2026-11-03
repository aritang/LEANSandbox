# LEANSandbox

## Creating a subproject

Run everything from `~/LEANSandbox`. Folder names must start with a **capital letter** and contain no spaces or hyphens, because they become module names.

**1. Create the folder and a file**

```bash
mkdir ProjC
touch ProjC/Basic.lean
```

That's enough to start working. VS Code checks any `.lean` file inside `~/LEANSandbox/` live, using the project's toolchain and Mathlib, so `import Mathlib` works right away.

**2. Register it in `lakefile.toml`** (only needed when you want either of these)

- one file to import another, e.g. `import ProjC.Defs` (without this you get an "unknown module" error)
- `lake build` to compile the folder

```toml
[[lean_lib]]
name = "ProjC"
globs = ["ProjC.+"]
```

`ProjC.+` means every `.lean` file inside `ProjC/`, including nested subfolders.

Rule of thumb: skip this for a single scratch file; do it for any project that will have more than one file.

**3. Build** (optional; not needed for interactive work)

```bash
lake build ProjC
```

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.
