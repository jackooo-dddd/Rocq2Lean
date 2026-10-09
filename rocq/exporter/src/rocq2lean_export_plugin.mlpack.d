src/rocq2lean_export_plugin_MLPACK_DEPENDENCIES:=src/r2l_json src/r2l_export src/g_rocq2lean_export
src/r2l_json.cmx : FOR_PACK=-for-pack Rocq2lean_export_plugin
src/r2l_export.cmx : FOR_PACK=-for-pack Rocq2lean_export_plugin
src/g_rocq2lean_export.cmx : FOR_PACK=-for-pack Rocq2lean_export_plugin
src/rocq2lean_export_plugin.cmo:$(addsuffix .cmo,$(src/rocq2lean_export_plugin_MLPACK_DEPENDENCIES))
src/rocq2lean_export_plugin.cmx:$(addsuffix .cmx,$(src/rocq2lean_export_plugin_MLPACK_DEPENDENCIES))
