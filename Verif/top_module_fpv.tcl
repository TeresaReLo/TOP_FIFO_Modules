clear -all
set design_top top_module
#lista de archivos que queremos compilar (RTL)
analyze -sv -f rtl_verif.flist 
analyze -sv -f verif_fv.flist
elaborate -top $design_top -create_related_covers {precondition witness} -x_value 0
clock clk
reset rst -non_resettable_regs 0

