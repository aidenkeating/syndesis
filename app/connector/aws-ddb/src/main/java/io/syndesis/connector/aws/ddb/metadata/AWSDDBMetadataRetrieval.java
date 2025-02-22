/*
 * Copyright (C) 2016 Red Hat, Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package io.syndesis.connector.aws.ddb.metadata;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import com.amazonaws.services.dynamodbv2.model.AttributeValue;
import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.module.jsonSchema.factories.JsonSchemaFactory;
import com.fasterxml.jackson.module.jsonSchema.types.ObjectSchema;
import com.google.common.base.Splitter;
import io.syndesis.common.model.DataShape;
import io.syndesis.common.model.DataShapeKinds;
import io.syndesis.common.model.DataShapeMetaData;
import io.syndesis.common.util.Json;
import io.syndesis.connector.aws.ddb.util.Util;
import io.syndesis.connector.support.util.ConnectorOptions;
import io.syndesis.connector.support.verifier.api.ComponentMetadataRetrieval;
import io.syndesis.connector.support.verifier.api.PropertyPair;
import io.syndesis.connector.support.verifier.api.SyndesisMetadata;
import org.apache.camel.CamelContext;
import org.apache.camel.component.extension.MetaDataExtension;
import org.apache.camel.component.extension.MetaDataExtension.MetaData;

/**
 * Extract all automatic info (column names) to enrich the properties.
 */
public final class AWSDDBMetadataRetrieval extends ComponentMetadataRetrieval {

    @Override
    protected MetaDataExtension resolveMetaDataExtension(CamelContext context,
                                                         Class<? extends MetaDataExtension> metaDataExtensionClass,
                                                         String componentId,
                                                         String actionId) {
        return new AWSDDBConnectorMetaDataExtension(context);
    }


    @Override
    protected SyndesisMetadata adapt(CamelContext context, String componentId, String actionId,
                                     Map<String, Object> properties, MetaData metadata) {

        return adaptForDDB(properties);
    }

    /**
     * Extract columns of query and result to create a data shape.
     *
     * @param properties
     * @return
     */
    private SyndesisMetadata adaptForDDB(final Map<String, Object> properties) {
        final Map<String, List<PropertyPair>> enrichedProperties = new HashMap<>();

        Map<String, AttributeValue> element = Util.getAttributeValueMap("element", properties);

        List<String> attributes = new ArrayList<String>();
        String optionAttributes = ConnectorOptions.extractOption(properties, "attributes", "");
        if (!optionAttributes.isEmpty()) {
            Splitter splitter = Splitter.on(',');
            splitter = splitter.trimResults();
            splitter = splitter.omitEmptyStrings();
            attributes = splitter.splitToList(optionAttributes);
        }

        //fallback to use the list of attributes on the filter
        //this is used always on put-item
        if (attributes.isEmpty()) {
            attributes.addAll(element.keySet());
        }

        // build the input and output schemas
        final JsonSchemaFactory factory = new JsonSchemaFactory();
        final ObjectSchema builderIn = new ObjectSchema();
        builderIn.setTitle("Parameters");

        Set<Map.Entry<String, AttributeValue>> elements = element.entrySet();
        elements.removeIf(e -> !Util.getValue(e.getValue()).toString().startsWith(":"));

        for (Map.Entry<String, AttributeValue> inParam : elements) {
            builderIn.putOptionalProperty(Util.getValue(inParam.getValue()).toString(), factory.stringSchema());
        }

        final ObjectSchema builderOut = new ObjectSchema();
        builderOut.setTitle("Result");
        for (String outParam : attributes) {
            builderOut.putOptionalProperty(outParam, factory.stringSchema());
        }

        try {
            DataShape.Builder inDataShapeBuilder = new DataShape.Builder().type(builderIn.getTitle());
            if (builderIn.getProperties().isEmpty()) {
                inDataShapeBuilder.kind(DataShapeKinds.NONE);
            } else {
                inDataShapeBuilder.kind(DataShapeKinds.JSON_SCHEMA)
                    .name("Parameters")
                    .description(String.format("Query parameters."))
                    .specification(Json.writer().writeValueAsString(builderIn));

                inDataShapeBuilder.putMetadata(DataShapeMetaData.VARIANT, DataShapeMetaData.VARIANT_ELEMENT);

            }
            DataShape.Builder outDataShapeBuilder = new DataShape.Builder().type(builderOut.getTitle());
            if (builderOut.getProperties().isEmpty()) {
                outDataShapeBuilder.kind(DataShapeKinds.NONE);
            } else {
                outDataShapeBuilder.kind(DataShapeKinds.JSON_SCHEMA)
                    .name("Result")
                    .description(String.format("Attributes on the result."))
                    .putMetadata(DataShapeMetaData.VARIANT, DataShapeMetaData.VARIANT_COLLECTION)
                    .specification(Json.writer().writeValueAsString(builderOut));
            }

            return new SyndesisMetadata(enrichedProperties,
                inDataShapeBuilder.build(), outDataShapeBuilder.build());
        } catch (JsonProcessingException e) {
            throw new IllegalStateException(e);
        }
    }
}
