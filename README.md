# Programming Languages, SNU 4190.310, 2016 Fall

- Instructor: Prof. [Chung-Kil Hur](http://sf.snu.ac.kr/gil.hur)
- TA: [Jeehoon Kang](http://sf.snu.ac.kr/jeehoon.kang), [Juneyoung Lee](http://sf.snu.ac.kr/juneyoung.lee)
    + Email address: [pl201602@sf.snu.ac.kr](mailto:pl201602@sf.snu.ac.kr).
        * Send emails for administrative matters only. Use the [GitHub repository issue tracker](https://github.com/snu-sf-class/pl201602/issues).
        * *DO NOT* send emails to `jee...@sf.snu.ac.kr` and `jun...@sf.snu.ac.kr`.
        * In the case of sending TA an email, specify sender's name and student ID.
    + Place: Bldg 301 Rm 416
    + Office Hour: TBA.  In the case of needing an extra time, please email me to make an appointment.

## Announcements

TBA

## Assignments

| Due        	| Due (Delay)	| Description                   	 	 	 	 	 	 	 	 	 	 	 	 	 	| Points 	|
|------------	|------------	|-----------------------------------------------------------------------------------	|-------	|

## Must Read

- *READ VERY CAREFULLY* this section.

### Grading

- Assignments: 45%
    + Coq problems in the [software foundations material](http://www.cis.upenn.edu/~bcpierce/sf/current/index.html). Read carefully the next subsections.
- Exams: 50% (mid-term 20% and final 30%)
    + You will solve Coq problems at the lab during the exam.
- Attendance: 5%
    + -1% per absence.  *IMPORTANT: 6 absences make an F*.

### Questions

- Ask questions in the [GitHub repository issue tracker](https://github.com/snu-sf-class/pl201602/issues).
- Send email for *PERSONAL MATTERS ONLY*.
- If you want to post a piece of source code, please DO NOT upload an image of it. Because it is hard to parse images.
    + Instead, use GitHub Markdown's ["fenced code blocks" feature](https://help.github.com/articles/github-flavored-markdown/#fenced-code-blocks).
    + Or, you can always use [GitHub Gist](https://gist.github.com/).

### Coq

- Use Coq [8.5pl2](https://coq.inria.fr).  *DO NOT* use other versions.
    + If not, your submissions (assignments & exams) will not be properly graded.

- Install Coq.
    + Installer (OS X / Windows)
        * Download [Binaries](https://coq.inria.fr/download) and install it.
        * Windows: after installing it, see below ("Cygwin For Windows").

    + Cygwin For Windows
        * Cygwin (for `make`). 
            - Download [Cygwin](https://cygwin.com/install.html).  *CAUTION*: choose 32- or 64-bit versions correctly.
            - Install Cygwin. Make sure that you install `bash` and `make` (in Select packages). Installation may take a long time.
            - Now by "terminal" we mean the Cygwin terminal.
        * Add the directory that contains Coq binaries in the `PATH` variable.
            - Edit your Shell init file (like `~/.bashrc` or `~/.bash_profile`).
            - Find the file in `C:\cygwin\home\[USER_ID]`.
            - Add `export PATH=$PATH:/cygdrive/c/Program\ Files\ \(x86\)/Coq/bin/` at the end of the file. The directory to add may be different for your environment.
            - Restart the terminal to apply `~/.bashrc`.
            - Check `which coqc` in the terminal. It should point to the `coqc` binary.

    + OPAM (Linux / OS X)
        * Install necessary libraries.
            - OS X

                    # install brew (http://brew.sh/index.html)
                    brew install gtksourceview

            - CentOS-like Linux

                    sudo yum install gtksourceview2-devel

            - Debian-like Linux

                    sudo apt-get install liblablgtksourceview2-ocaml-dev

        * Install [opam](http://opam.ocaml.org/doc/Install.html), and make sure you can use OCaml 4.03.0.
        * `opam init --comp 4.03.0`
        * `opam install coqide.8.5.2`
        * Test by `coqc -v` in the command line. Check your `PATH` variable if you get an error.
        * Run CoqIDE by `coqide`.

- Use IDEs supporting Coq.
    + CoqIDE: installed by default.
    + Emacs: [Company-Coq](https://github.com/cpitclaudel/company-coq). Follow the setup instructions.
    + Vim: [Coquille](https://github.com/the-lambda-church/coquille). See the troubleshootings below.

### Textbook: Software Foundations

- The textbook is in this repository's `sf/` directory.
- *DO NOT DOWNLOAD* the textbook from [The official Software Foundation website](https://www.cis.upenn.edu/~bcpierce/sf/current/index.html) in order to keep in sync.

### Assignment

- Assignments will be issued every Wednesday.  The deadline is the next Sunday (10 days later).  The deadline for the delayed submission is the next to the next Sunday (17 days later).

#### Honor Code: *DO NOT CHEAT*

- If you copy others' source code, you will get F.
- "Others' source code" includes other students' and resources around the web. Especially, do not consult with public repositories on software foundations.
- Note that we have a good automatic clone detector. We found out that a lot of students cheated last time. We hope we all be happy at the end of the semester..
- The maximum score of a delayed submission is 80% that of a regular submission.
    + The granularity the delayed submission is per-problem, not per-assignment. So even if you couldn't get the full score for the regular submission period, try to solve the remaining problems and submit them.

#### Submission

- `assignments/$NAME` directory is the assignment `$NAME`.
    + You submit `P??.v` files.  You should edit only `P??.v`. *DO NOT TOUCH ANYTHING ELSE*.
    + `E??.v` files are for evaluation.
    + Everything else are for relevant the definitions for the assignment.
- `make` in the terminal to compile files so that IDE can understand them.
- Edit `P??.v` files to do the assignment.
- `make` in the terminal to compile your submission.  `make eval` in the terminal to grade your submission yourself. 
- Both `make` and `make eval` *SHOULD SUCCEED*. If not, your score will be 0.
- `make eval` will check your submission.
    + `P??.v` files *SHOULD NOT* contain `admit`, `Admitted`, and anything in `forbidden.txt`.
    + If a `P??.v` file contains string `GIVEUP`, then it will be scored 0.
- `make submission` to prepare your submission.
    + `zip` should be installed. Otherwise, you can just zip `P??.v`.
- ~~Submit at: http://147.46.219.145:8100/~~ TBA
    + *DO NOT ATTACK*. Please.
    + *DO NOT USE A STRONG PASSWORD*. It is `http`.
    + If your submission status is `SYSTEM ERROR` or `RUNNING` for a long time, even after refreshing your web browser for several times, please ask the TA.

### Troubleshootings

- If something bad happens, please download the most recent version of the assignments.
- You may have to `make` before interacting with IDEs.
- You can specify the CRLF handling strategy in Git ([cf](http://stackoverflow.com/questions/170961/whats-the-best-crlf-carriage-return-line-feed-handling-strategy-with-git)). In Windows, some strategies may break the Makefile. Please just use the linebreaks as in the repository.
- ~~When running CoqIDE in OS X for the first time, you may see an error message saying `Failed to load coqtop.` Then click `No`, and then find `/Applications/CoqIDE_8.4pl5.app/Contents/Resources/bin/coqtop` and open for once. Then goto `CoqIDE` > `Preferences` > `Externals`. And then change `coqtop` into `/Applications/CoqIDE_8.4pl5.app/Contents/Resources/bin/coqtop`.~~
- Your submission file should have alphanumeric characters only.
- If cygwin complains like `./check.sh: line 2: $'\r': command not found`, please:
    + Install `dos2unix` in Cygwin.
    + Run: `dos2unix check.sh`
- If you use Coquille (on Vim) and your terminal is hidden by some message (`warning (some rule has been masked)`), please edit `~/.vim/.../coquille/autoload/coquille.py`'s `restart_coq` as follows (NOTE: `stderr = subprocess.PIPE`):

        def restart_coq(*args):
        global coqtop
        if coqtop: kill_coqtop()
        try:
            coqtop = subprocess.Popen(
                    ["coqtop", "-ideslave"] + list(args),
                    stdin = subprocess.PIPE,
                    stdout = subprocess.PIPE,
                    stderr = subprocess.PIPE,
                    preexec_fn = ignore_sigint
                    )
        except OSError:
            print("Error: couldn't launch coqtop")

  Thank you for reporting, @indiofish

### Misc.

- I strongly recommend you to use [Git](http://git-scm.com/) for the course. Register at [GitHub](https://github.com). [Try Git](https://try.github.io/levels/1/challenges/1).
