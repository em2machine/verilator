#!/usr/bin/env python3
# DESCRIPTION: Protected template writes fail before changing their target.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t/t_EXAMPLE.v"

test.lint(verilator_flags2=["--debug", "--debugi", "0", "--debug-template-protect-test-write"],
          fails='any')

test.file_grep(test.compile_log_filename,
               r"Protected template write: name; owner MODULE 'template_fixture'; target BEGIN 'template_original'")
test.file_grep_not(test.compile_log_filename, r"target BEGIN 'template_changed'")

test.passes()
