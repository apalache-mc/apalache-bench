from benchexec.tools.template import BaseTool2
import benchexec.result as result


class Tool(BaseTool2):
    """
    Tool info for Apalache
    https://apalache.informal.systems/
    """

    def name(self):
        return "Apalache"

    def executable(self, tool_locator):
        return tool_locator.find_executable("apalache-mc")

    def version(self, executable):
        return self._version_from_tool(executable, arg="version").strip()

    def determine_result(self, run):
        return {
            255: "PARSING ERROR",
            12: result.RESULT_FALSE_PROP,
            0: result.RESULT_TRUE_PROP,
        }.get(run.exit_code.value, result.RESULT_ERROR)

    ## TODO OVerride
    # def get_value_from_output(self, output, identifier):
