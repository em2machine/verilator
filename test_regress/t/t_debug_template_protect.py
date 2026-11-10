#!/usr/bin/env python3
# DESCRIPTION: Protected templates produce independent writable clones.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')
test.top_filename = "t/t_EXAMPLE.v"

test.lint(verilator_flags2=["--debug", "--debugi", "0", "--debugi-Verilator", "2",
                           "--debug-self-test"])
test.file_grep(test.compile_log_filename, r"selfTest done")

test.passes()
