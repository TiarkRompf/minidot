#!/usr/bin/awk -f

### script to sync dot.elf with dev
###
### usage examples:
### ./bin/sync.awk src/main/elf/dot.elf >dev/test15q.elf
### ./bin/sync.awk dev/test15q.elf >src/main/elf/dot.elf

{
    ### uncomment lines starting with % ++
    if (substr($0, 0, 4) == "% ++")
        print substr($0, 6), "% --"
    ### comment lines ending with % --
    else if (substr($0, length($0)-3) == "% --")
        print "% ++", substr($0, 0, length($0)-5)
    ### remove twelf EOF
    else if ($0 == "%.")
        print "% EOF"
    ### add twelf EOF
    else if ($0 == "% EOF")
        print "%."
    else
        print $0
}
