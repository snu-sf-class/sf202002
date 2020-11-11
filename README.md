# Software Foundations, SNU M1522.001200, 2020 Fall

- Instructor: Prof. [Chung-Kil Hur](http://sf.snu.ac.kr/gil.hur)
    + Email address: gil.hur@sf.snu.ac.kr
    + Office: 302-426
- TA: [Dongjoo Kim](http://sf.snu.ac.kr/dongjoo.kim)
    + Email address: sf@sf.snu.ac.kr
    + Office: 302-312-2
- Class material: http://www.cis.upenn.edu/~bcpierce/sf/current/index.html
- Please use email to ask questions (Don't use GitHub Issues)

## Announcements

- Nov. 12: Extend assignment 3's deadline.
- Nov. 09: Assignment 3 is uploaded.
- Oct. 25: [Midterm results](https://github.com/snu-sf-class/sf202002/blob/master/MidtermResults.pdf) is uploaded. We will support about missing files by checking in person. So if you want to check or have any other questions, email TA(sf@sf.snu.ac.kr).
- Oct. 22: [Midterm exam announcement](https://github.com/snu-sf-class/sf202002/blob/master/MidtermInstruction.md)
- Oct. 22: Assignment 2 is uploaded.
- Oct. 7: Submission server is opened.
- Sep. 29: Midterm will be held on Oct. 24th Sat, 1 - 5 pm
- Sep. 25: Assignment 1 is uploaded.

## Assignments

- Download skeleton code and replace `FILL_IN_HERE` with your code in P**.v.
- Visit http://147.46.245.103:8000 and log-in with your id (e.g. 2016-12345). Your initial password is equivalent to your id.
- Change your password before submitting your assignments.
- If you forget your password, email to ta(sf@sf.snu.ac.kr).
- Use 'make submission' command and attach the zip file.
- No delayed submission.
- Claims: within 2 weeks from the due date, please.


| Due        	| Description                   	 	 	 	 	 	 	 	 	 	 	 	 	 	|
|------------	|-----------------------------------------------------------------------------------
| Oct.9 23:59  	| Assignment 1 - Basic & Induction 	 	 	 	 	 	 	 	 	 	 	 	 	 	|
| Nov.6 23:59   | Assignment 2 - Lists & Poly & Logic                         |
| Nov.26 23:59  | Assignment 3 - IndProp & Imp                                |

## Grading(tentative)
- Attendance: 5%
- Assignments: 25%
- Mid-term: 30%
- Final: 40%

## Coq

- Install Coq [8.12.0](https://coq.inria.fr).
    + Using an installer (Windows, MacOS)
        * Download [Binaries](https://coq.inria.fr/download) and install it.

    + Using OPAM (Linux / MacOS)
        * OPAM is OCaml package manager, and you can use it to install Coq in Linux.
        * See [https://coq.inria.fr/opam/www/using.html](https://coq.inria.fr/opam/www/using.html).

    + Using brew (MacOS)
        * Run `brew install coq`.
        * Note this wouldn't install CoqIDE.

- Install IDE for Coq.
    + CoqIDE: installed by default.
    + Emacs: [Company-Coq](https://github.com/cpitclaudel/company-coq). Follow the setup instructions.
        * If it shows `Searching for program No such file or directory coqtop` error, please add `(custom-set-variables '(coq-prog-name "PATH/TO/coqtop"))` to `.emacs` file.
        * In case of MacOS, coqtop is at `/Applications/CoqIDE_8.9.1.app/Contents/Resources/bin/`.

#### Honor Code: *DO NOT CHEAT*
- Do not copy others' source code, including other students' and resources around the web. Especially, do not consult with public repositories on software foundations.
- Assignment score will be adjusted with the exam score. See above.
