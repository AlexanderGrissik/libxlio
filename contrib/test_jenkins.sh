#!/bin/bash -El
#
# Testing script for XLIO, to run from Jenkins CI
#
# Copyright (C) Mellanox Technologies Ltd. 2001-2020.  ALL RIGHTS RESERVED.
#
# See file LICENSE for terms.
#
#
# Environment variables set by Jenkins CI:
#  - WORKSPACE         : path to working directory
#  - BUILD_NUMBER      : jenkins build number
#  - TARGET            : target configuration
#

echo "======================================================"
echo
echo "# starting on host --------->  $(hostname 2>/dev/null) "
echo "# arguments called with ---->  ${@}        "
echo "# path to me --------------->  ${0}        "
echo "# parent path -------------->  ${0%/*}     "
echo "# name --------------------->  ${0##*/}    "
echo

PATH=${PATH}:/hpc/local/bin:/hpc/local/oss/vma/
MODULEPATH=${MODULEPATH}:/hpc/local/etc/modulefiles

echo
for f in autoconf automake libtool ; do $f --version | head -1 ; done
echo

rel_path=$(dirname $0)
abs_path=$(readlink -f $rel_path)

echo
echo "# rel_path ----------------->  ${rel_path}    "
echo "# abs_path ----------------->  ${abs_path}       "
echo

source ${abs_path}/jenkins_tests/globals.sh

echo
echo "# WORKSPACE ---------------->  ${WORKSPACE}    "
echo "# BUILD_NUMBER ------------->  ${BUILD_NUMBER} "
echo "# TARGET ------------------->  ${TARGET}       "
echo

# Values: none, fail, always
#
jenkins_opt_artifacts=${jenkins_opt_artifacts:="always"}

# Values: 0..N test (max 100)
#
jenkins_opt_exit=${jenkins_opt_exit:="6"}

# Test scenario list
#
jenkins_test_build=${jenkins_test_build:="no"}

jenkins_test_compiler=${jenkins_test_compiler:="no"}
jenkins_test_rpm=${jenkins_test_rpm:="no"}
jenkins_test_cov=${jenkins_test_cov:="no"}
jenkins_test_cppcheck=${jenkins_test_cppcheck:="no"}
jenkins_test_csbuild=${jenkins_test_csbuild:="no"}
jenkins_test_run=${jenkins_test_run:="no"}
jenkins_test_gtest=${jenkins_test_gtest:="no"}
jenkins_test_vg=${jenkins_test_vg:="no"}
jenkins_test_style=${jenkins_test_style:="no"}
jenkins_test_tool=${jenkins_test_tool:="no"}
jenkins_test_commit=${jenkins_test_commit:="no"}

echo
for var in ${!jenkins_test_@}; do
   printf "%s%q\n" "$var=" "${!var}"
done
echo

# check go/not go
#
do_check_env
echo
echo "======================================================"
set -xe

cd $WORKSPACE

if [ $BUILD_NUMBER -le 0 ]; then
    rm -rf ${WORKSPACE}/${prefix}
    rm -rf autom4te.cache
fi

if [ ! -e configure ] && [ -e autogen.sh ]; then
    ./autogen.sh -s
fi

for target_v in "${target_list[@]}"; do
    ret=0
    IFS=':' read target_name target_option <<< "$target_v"

    export jenkins_test_artifacts="${WORKSPACE}/${prefix}/xlio-${BUILD_NUMBER}-$(hostname -s)-${target_name}"
    export jenkins_test_custom_configure="${target_option}"
    export jenkins_target="${target_name}"
    set +x
    echo "======================================================"
    echo "Jenkins is checking for [${target_name}] target ..."
    echo "======================================================"
    set -x

    # check building and exit immediately in case failure
    #
    if [ "$jenkins_test_build" = "yes" ]; then
        $WORKSPACE/contrib/jenkins_tests/build.sh
        ret=$?
        if [ $ret -gt 0 ]; then
           do_err "case: [build: ret=$ret]"
        fi
        rc=$((rc + $ret))
    fi

    # check other units w/o forcing exiting
    #
    set +e
    if [ 1 -lt "$jenkins_opt_exit" -o "$rc" -eq 0 ]; then
	    if [ "$jenkins_test_compiler" = "yes" ]; then
	        $WORKSPACE/contrib/jenkins_tests/compiler.sh
	        ret=$?
	        if [ $ret -gt 0 ]; then
	           do_err "case: [compiler: ret=$ret]"
	        fi
	        rc=$((rc + $ret))
	    fi
    fi
    if [ 2 -lt "$jenkins_opt_exit" -o "$rc" -eq 0 ]; then
	    if [ "$jenkins_test_rpm" = "yes" ]; then
	        $WORKSPACE/contrib/jenkins_tests/rpm.sh
	        ret=$?
	        if [ $ret -gt 0 ]; then
	           do_err "case: [rpm: ret=$ret]"
	        fi
	        rc=$((rc + $ret))
	    fi
	fi
    if [ 3 -lt "$jenkins_opt_exit" -o "$rc" -eq 0 ]; then
	    if [ "$jenkins_test_cov" = "yes" ]; then
	        $WORKSPACE/contrib/jenkins_tests/cov.sh
	        ret=$?
	        if [ $ret -gt 0 ]; then
	           do_err "case: [cov: ret=$ret]"
	        fi
	        rc=$((rc + $ret))
	    fi
    fi
    if [ 4 -lt "$jenkins_opt_exit" -o "$rc" -eq 0 ]; then
	    if [ "$jenkins_test_cppcheck" = "yes" ]; then
	        $WORKSPACE/contrib/jenkins_tests/cppcheck.sh
	        ret=$?
	        if [ $ret -gt 0 ]; then
	           do_err "case: [cppcheck: ret=$ret]"
	        fi
	        rc=$((rc + $ret))
	    fi
    fi
    if [ 5 -lt "$jenkins_opt_exit" -o "$rc" -eq 0 ]; then
	    if [ "$jenkins_test_csbuild" = "yes" ]; then
	        $WORKSPACE/contrib/jenkins_tests/csbuild.sh
	        ret=$?
	        if [ $ret -gt 0 ]; then
	           do_err "case: [csbuild: ret=$ret]"
	        fi
	        rc=$((rc + $ret))
	    fi
    fi
    if [ 6 -lt "$jenkins_opt_exit" -o "$rc" -eq 0 ]; then
	    if [ "$jenkins_test_run" = "yes" ]; then
	        $WORKSPACE/contrib/jenkins_tests/test.sh
	        ret=$?
	        if [ $ret -gt 0 ]; then
	           do_err "case: [test: ret=$ret]"
	        fi
	        rc=$((rc + $ret))
	    fi
    fi
    if [ 7 -lt "$jenkins_opt_exit" -o "$rc" -eq 0 ]; then
	    if [ "$jenkins_test_gtest" = "yes" ]; then
	        $WORKSPACE/contrib/jenkins_tests/gtest.sh
	        ret=$?
	        if [ $ret -gt 0 ]; then
	           do_err "case: [gtest: ret=$ret]"
	        fi
	        rc=$((rc + $ret))
	    fi
    fi
    if [ 8 -lt "$jenkins_opt_exit" -o "$rc" -eq 0 ]; then
	    if [ "$jenkins_test_vg" = "yes" ]; then
	        $WORKSPACE/contrib/jenkins_tests/vg.sh
	        ret=$?
	        if [ $ret -gt 0 ]; then
	           do_err "case: [vg: ret=$ret]"
	        fi
	        rc=$((rc + $ret))
	    fi
    fi
    if [ 9 -lt "$jenkins_opt_exit" -o "$rc" -eq 0 ]; then
	    if [ "$jenkins_test_style" = "yes" ]; then
	        $WORKSPACE/contrib/jenkins_tests/style.sh
	        ret=$?
	        if [ $ret -gt 0 ]; then
	           do_err "case: [style: ret=$ret]"
	        fi
	        rc=$((rc + $ret))
	    fi
    fi
    if [ 10 -lt "$jenkins_opt_exit" -o "$rc" -eq 0 ]; then
	    if [ "$jenkins_test_tool" = "yes" ]; then
	        $WORKSPACE/contrib/jenkins_tests/tool.sh
	        ret=$?
	        if [ $ret -gt 0 ]; then
	           do_err "case: [tool: ret=$ret]"
	        fi
	        rc=$((rc + $ret))
	    fi
    fi
    if [ 11 -lt "$jenkins_opt_exit" -o "$rc" -eq 0 ]; then
	    if [ "$jenkins_test_commit" = "yes" ]; then
	        $WORKSPACE/contrib/jenkins_tests/commit.sh
	        ret=$?
	        if [ $ret -gt 0 ]; then
	           do_err "case: [commit: ret=$ret]"
	        fi
	        rc=$((rc + $ret))
	    fi
    fi
    set -e

    if [ "$jenkins_opt_artifacts" == "always" ] || [ "$jenkins_opt_artifacts" == "fail" -a "$rc" -gt 0 ]; then

        # Archive all logs in single file
        do_archive "${WORKSPACE}/${prefix}/${target_name}/*.tap"

	    set +x
	    gzip -f "${jenkins_test_artifacts}.tar"
	    echo "======================================================"
	    echo "Jenkins result for [${target_name}] target: return $rc"
	    echo "Artifacts: ${jenkins_test_artifacts}.tar.gz"
	    echo "======================================================"
	    set -x
    fi

done

rm -rf $WORKSPACE/config.cache

echo "[${0##*/}]..................exit code = $rc"
exit $rc
