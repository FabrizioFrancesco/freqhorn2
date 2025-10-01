add_executable (xaihorn XAIHorn.cpp)
target_link_libraries (xaihorn ${Z3_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${GMPXX_LIB} ${GMP_LIB} ${ARMADILLO_LIBRARIES})
install(TARGETS xaihorn RUNTIME DESTINATION bin)
