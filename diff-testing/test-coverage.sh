#!/usr/bin/env bash
set -euo pipefail

raco cross -q --workspace /workspace/rosette-4 racket patcher.rkt ./patch/incorrect_and.patch ./generation/prog100208336541399653250221187751391297369.rkt

git reset --hard

raco cross -q --workspace /workspace/rosette-4 racket patcher.rkt ./patch/incorrect_or.patch ./generation/prog100026410668776740492900673318090171927233255361720922983271273849413253676502727166331182369672360102050306966877856993674940497.rkt

git reset --hard

raco cross -q --workspace /workspace/rosette-4 racket patcher.rkt ./patch/incorrect_lt.patch ./generation/prog735983.rkt

git reset --hard

raco cross -q --workspace /workspace/rosette-4 racket patcher.rkt ./patch/incorrect_call_op.patch ./generation/prog666831569393266787587089860792333636466692132130.rkt

git reset --hard

raco cross -q --workspace /workspace/rosette-4 racket patcher.rkt ./patch/incorrect_call.patch ./generation/prog478473500332049125701102687487886134892618785332689813519393109671586439862663588789828131845030156.rkt

git reset --hard

raco cross -q --workspace /workspace/rosette-4 racket patcher.rkt ./patch/incorrect_call_bad.patch ./generation/prog16803.rkt

git reset --hard

raco cross -q --workspace /workspace/rosette-4 racket patcher.rkt ./patch/incorrect_let.patch ./generation/prog271706286423030047271490064405043091576078507211894322485583089278608494173230103175221675458186681751625690187786390.rkt

git reset --hard

raco cross -q --workspace /workspace/rosette-4 racket patcher.rkt ./patch/incorrect_if_sym.patch ./generation/prog15.rkt

git reset --hard

raco cross -q --workspace /workspace/rosette-4 racket patcher.rkt ./patch/incorrect_if_true_false.patch ./generation/prog1331343393596762924043919245445877806201864368967369509032193564215325013490794460521988648842748377343143771160948246706431109369.rkt

git reset --hard

raco cross -q --workspace /workspace/rosette-4 racket patcher.rkt ./patch/incorrect_error.patch ./generation/prog19436053114232394.rkt

git reset --hard

raco cross -q --workspace /workspace/rosette-4 racket patcher.rkt ./patch/incorrect_abort.patch ./generation/prog23160718406451015591104819237807520888040421765198.rkt

git reset --hard

cat ./workspace/incorrect_*.rktd > ./workspace/log.rktd

raco cross -q --workspace /workspace/rosette-4 racket report.rkt
